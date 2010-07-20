{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances #-}

module Language.Javascript.JMacro.TypeCheck where

import Language.Javascript.JMacro.Base
import Language.Javascript.JMacro.Types
import Language.Javascript.JMacro.QQ

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.State
import Control.Monad.Error
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S


data Constraint = Sub JType
                | Disjunction Constraint Constraint
                  deriving (Eq, Ord, Show)

data StoreVal = SVType JType
              | SVConstrained (Set Constraint)
                deriving Show

data TCState = TCS {tc_env :: [Map Ident JType],
                    tc_vars :: Map Int StoreVal,
                    tc_varCt :: Int} deriving Show

tcStateEmpty = TCS [M.empty] M.empty 0

newtype TMonad a = TMonad (ErrorT String (State TCState) a) deriving (Functor, Monad, MonadState TCState, MonadError String, Applicative)

instance Applicative (ErrorT String (State TCState)) where
    pure = return
    (<*>) = ap

runTMonad (TMonad x) = evalState (runErrorT x) tcStateEmpty

runTypecheck x = runTMonad . typecheck $ x

prettyType :: JsToDoc a => a -> TMonad String
prettyType x = return $ show $ jsToDoc x


tyErr1 :: JsToDoc a => String -> a -> TMonad b
tyErr1 s t = do
  st <- prettyType t
  throwError $ s ++ ": " ++ st

tyErr2 :: String -> JType -> JType -> TMonad a
tyErr2 s t t' = do
  st <- prettyType t
  st' <- prettyType t'
  throwError $ s ++ ". Expected: " ++ st ++ ", Inferred: " ++ st'

newVarRef :: TMonad VarRef
newVarRef = do
  v <- tc_varCt <$> get
  modify (\s -> s {tc_varCt = v + 1})
  return $ (Nothing, v)

newTyVar :: TMonad JType
newTyVar = JTFree <$> newVarRef

newNamedTyVar :: String -> TMonad JType
newNamedTyVar n = JTFree . first (const $ Just n) <$> newVarRef


addEnv :: Ident -> JType -> TMonad ()
addEnv ident typ = do
  envstack <- tc_env <$> get
  case envstack of
    (e:es)
        | M.lookup ident e == Nothing -> modify (\s -> s {tc_env = M.insert ident typ e : es})
        | otherwise -> tyErr1 "Identifier already bound" ident
    _ -> throwError "empty env stack (this should never happen)"

newVarDecl :: Ident -> TMonad JType
newVarDecl ident = do
  v <- newTyVar
  addEnv ident v
  return v

newConstrainedTyVar :: TMonad JType
newConstrainedTyVar = do
  v@(_,ref) <- newVarRef
  vars <- tc_vars <$> get
  modify (\s -> s {tc_vars = M.insert ref (SVConstrained S.empty) vars})
  return $ JTFree v


addConstraint :: Constraint -> VarRef -> TMonad ()
addConstraint c (mbName,ref) = do
     vars <- tc_vars <$> get
     case M.lookup ref vars of
       (Just (SVConstrained cs)) -> modify (\s -> s {tc_vars = M.insert ref (SVConstrained $ insConstraint c cs) vars})
       Nothing -> modify (\s -> s {tc_vars = M.insert ref (SVConstrained $ S.singleton c) vars})
       _ -> throwError $ "attempt to add constraint to rigid type" ++ show c ++ ", " ++ show (mbName, ref)
    where
      insConstraint c cs = S.insert c cs --make me smarter!

resolveType :: JType -> TMonad JType
resolveType rt = do
     vs <- tc_vars <$> get
     go vs rt
  where
    go vars x@(JTFree (mbName, ref)) =
        case M.lookup ref vars of
          Just (SVType t) -> go vars t
          _ -> return x
    go vars (JTFunc args res) =
        JTFunc <$> mapM (go vars) args <*> go vars res
    go vars (JTList t) = JTList <$> go vars t
    go vars (JTMap  t) = JTMap  <$> go vars t
    go vars (JTRecord vref xs) =
        JTRecord vref . M.fromList <$> mapM (\(n,t) -> (\x->(n,x)) <$> go vars t) (M.toList xs)
    go _ x = return x

lookupEnv :: Ident -> TMonad JType
lookupEnv ident = resolveType =<< go . tc_env =<< get
    where go (e:es) = case M.lookup ident e of
                        Just t -> return t
                        Nothing -> go es
          go _ = tyErr1 "unable to resolve variable name: " ident

--subtype of a free variable is what!?
(<:) :: JType -> JType -> TMonad ()
x <: y = do
     xt <- resolveType x
     yt <- resolveType y
     if xt == yt
        then return ()
        else go xt yt
  where
    go (JTFree ref) yt = addConstraint (Sub yt) ref
    go xt@(JTFunc argsx retx) yt@(JTFunc argsy rety) = do
           when (length argsy < length argsx) $ tyErr2 "Couldn't subtype" xt yt
           zipWithM_ (<:) argsy argsx -- functions are contravariant in argument type
           retx <: rety -- functions are covariant in return type
    go (JTList xt) (JTList yt) = go xt yt
    go (JTMap xt) (JTMap yt) = go xt yt
    go (JTRecord _ _) (JTRecord _ _) = error "jtrecord"
    go xt yt = tyErr2 "Couldn't subtype" xt yt

class JTypeCheck a where
    typecheck :: a -> TMonad JType

instance JTypeCheck JExpr where
    typecheck (ValExpr e) = typecheck e
    typecheck (SelExpr e i) = undefined
    typecheck (IdxExpr e e1) = undefined
    typecheck (InfixExpr s e e1)
        | s `elem` ["-","/","*"] = setFixed JTNum >> return JTNum
        | s == "+" = setFixed JTNum >> return JTNum -- `orElse` setFixed JTStr --TODO: Intersection types
        | s `elem` [">","<","==","/="] = setFixed JTNum >> return JTBool
        | s `elem` ["||","&&"] = setFixed JTBool >> return JTBool
        | otherwise = throwError $ "Unhandled operator: " ++ s
        where setFixed t = do
                  (<: t) =<< typecheck e
                  (<: t) =<< typecheck e1


    typecheck (PostExpr s e) = undefined
    typecheck (IfExpr e e1 e2) = undefined
    typecheck (NewExpr e) = undefined
    typecheck (ApplExpr f args) = undefined
    typecheck (UnsatExpr _) = undefined --saturate (avoiding creation of existing ids) then typecheck
    typecheck (AntiExpr s) = fail $ "Antiquoted expression not provided with explicit signature: " ++ show s

instance JTypeCheck JVal where
    typecheck (JVar i) =
        case i of
          StrI "true" -> return JTBool
          StrI "false" -> return JTBool
          StrI "null"  -> newTyVar
          StrI _ -> lookupEnv i

    typecheck (JInt _) = return JTNum
    typecheck (JDouble _) = return JTNum
    typecheck (JStr _) = return JTString
    typecheck (JList _) = undefined --glball of xs
    typecheck (JRegEx _) = undefined --regex object
    typecheck (JHash mp) = JTRecord (Nothing,-1) . M.fromList <$> mapM go (M.toList mp)
        where go (n,v) = (\x -> (n,x)) <$> typecheck v
    typecheck (JFunc args body) = undefined --bring args into scope as constrained vars, typecheck body, typecheck args, return function + frame of all things to clone
    typecheck (UnsatVal _) = undefined --saturate (avoiding creation of existing ids) then typecheck


{-

data JType = JTNum
           | JTString
           | JTBool
           | JTStat
           | JTFunc [JType] (JType)
           | JTList JType
           | JTMap  JType
           | JTRecord VarRef [(String, JType)]
           | JTFree VarRef
             deriving (Eq, Ord, Read, Show, Typeable, Data)
-}

{-
instance JTypeCheck JVal where
    typecheck (JFunc args stat) =
                           withLocalScope args ( do
                             argst <- mapM (typecheck . JVar) args
                             rett <- typecheck stat
                             resC False $ JTFunc argst rett)
    typecheck (JHash m) = do
            let (is, es) = unzip $ M.toList m
            ets <- mapM typecheck es
            let initialrec
                    | null is = []
                    | otherwise =  zip (map StrI is) ets
            r@(JTRec i) <- newRec
            putRec i initialrec
            return r
    typecheck (JList es) = do
            (JTRec i) <- typecheck $ JHash $ M.fromList (zip (map show [1..]) es)
            es' <- mapM typecheck es
            e'' <- (Just <$> glball es') `orElse` return Nothing
            return $ JTList (Just i) e''
-}
{-
    -- | Values
data JVal = JVar     Ident
          | JDouble  Double
          | JInt     Integer
          | JStr     String
          | JList    [JExpr]
          | JRegEx   String
          | JHash    (M.Map String JExpr)
          | JFunc    [Ident] JStat
          | UnsatVal (State [Ident] JVal)
            deriving (Eq, Ord, Show, Data, Typeable)
-}

{-
data JExpr = ValExpr    JVal
           | SelExpr    JExpr Ident
           | IdxExpr    JExpr JExpr
           | InfixExpr  String JExpr JExpr
           | PostExpr   String JExpr
           | IfExpr     JExpr JExpr JExpr
           | NewExpr    JExpr
           | ApplExpr   JExpr [JExpr]
           | UnsatExpr  (State [Ident] JExpr)
           | AntiExpr   String
             deriving (Eq, Ord, Show, Data, Typeable)

-- | Statements
data JStat = DeclStat   Ident
           | ReturnStat JExpr
           | IfStat     JExpr JStat JStat
           | WhileStat  JExpr JStat
           | ForInStat  Bool Ident JExpr JStat
           | SwitchStat JExpr [(JExpr, JStat)] JStat
           | TryStat    JStat Ident JStat JStat
           | BlockStat  [JStat]
           | ApplStat   JExpr [JExpr]
           | PostStat   String JExpr
           | AssignStat JExpr JExpr
           | UnsatBlock (State [Ident] JStat)
           | AntiStat   String
           | TypeStat   (Either String Ident) JType
           | BreakStat
             deriving (Eq, Ord, Show, Data, Typeable)
-}