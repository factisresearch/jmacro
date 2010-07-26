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
import Data.List(intercalate)
import Data.Traversable hiding (sequence, mapM)
import qualified Data.Traversable as T
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S

-- Compos instance and utility
instance Compos JType where
    compos ret app f v =
        case v of
          JTFunc args body -> ret JTFunc `app` mapM' f args `app` f body
          JTList t -> ret JTList `app` f t
          JTMap t -> ret JTMap `app` f t
          JTRecord m -> ret JTRecord `app` m'
              where (ls,ts) = unzip $ M.toList m
                    m' = ret (M.fromAscList . zip ls) `app` mapM' f ts
          x -> ret x
      where
        mapM' g = foldr (app . app (ret (:)) . g) (ret [])

zipWithOrChange :: (a -> a -> b) -> (a -> b) -> [a] -> [a] -> [b]
zipWithOrChange f g xss yss = go xss yss
    where go (x:xs) (y:ys) = f x y : go xs ys
          go xs@(_:_) _ = map g xs
          go _ ys = map g ys

zipWithOrIdM :: Monad m => (a -> a -> m a) -> [a] -> [a] -> m [a]
zipWithOrIdM f xs ys = sequence $ zipWithOrChange f return xs ys


--constraints can be resolved if you can't assign to a value any further, which is the same as if you generalize.

-- Basic Types and TMonad
data Constraint = Sub JType
                | Super JType
                | Choice Constraint Constraint
                | GLB (Set JType)
                | LUB (Set JType)
                  deriving (Eq, Ord, Show)

data StoreVal = SVType JType
              | SVConstrained (Set Constraint)
                deriving Show

data TCState = TCS {tc_env :: [Map Ident JType],
                    tc_vars :: Map Int StoreVal,
                    tc_stack :: [Set Int],
                    tc_varCt :: Int} deriving Show

tcStateEmpty = TCS [M.empty] M.empty [S.empty] 0

newtype TMonad a = TMonad (ErrorT String (State TCState) a) deriving (Functor, Monad, MonadState TCState, MonadError String, Applicative)

instance Applicative (ErrorT String (State TCState)) where
    pure = return
    (<*>) = ap

class JTypeCheck a where
    typecheck :: a -> TMonad JType

evalTMonad (TMonad x) = evalState (runErrorT x) tcStateEmpty

runTMonad (TMonad x) = runState (runErrorT x) tcStateEmpty


-- Output prettyPrinters
prettyEnv :: TMonad [Map Ident String]
prettyEnv = do
  env <- tc_env <$> get
  mapM (T.mapM prettyType) env

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

tyErr2l :: String -> [JType] -> [JType] -> TMonad a
tyErr2l s t t' = do
  sts <- mapM prettyType t
  sts' <- mapM prettyType t'
  throwError $ s ++ ". Expected: (" ++ intercalate ", " sts ++
                 "), Inferred: (" ++ intercalate "," sts' ++")"

runTypecheckFull x = runTMonad $ do
                       r <- typecheck x
                       e <- prettyEnv
                       return (r,e)

runTypecheck x = evalTMonad . typecheck $ x

-- Manipulating VarRefs and Constraints
newVarRef :: TMonad VarRef
newVarRef = do
  v <- tc_varCt <$> get
  modify (\s -> s {tc_varCt = v + 1,
                   tc_stack = addStack v (tc_stack s)})
  return $ (Nothing, v)
      where addStack v (s:ss) = S.insert v s : ss
            addStack v _ = [S.singleton v]

newTyVar :: TMonad JType
newTyVar = JTFree <$> newVarRef

newNamedTyVar :: String -> TMonad JType
newNamedTyVar n = JTFree . first (const $ Just n) <$> newVarRef

newConstrainedTyVar :: TMonad JType
newConstrainedTyVar = do
  v@(_,ref) <- newVarRef
  vars <- tc_vars <$> get
  modify (\s -> s {tc_vars = M.insert ref (SVConstrained S.empty) vars})
  return $ JTFree v

lookupConstraints :: VarRef -> TMonad (Maybe (Set Constraint))
lookupConstraints (_,ref) = do
  vars <- tc_vars <$> get
  case M.lookup ref vars of
    (Just (SVConstrained cs)) -> return $ Just cs
    _ -> return Nothing

addConstraint :: Constraint -> VarRef -> TMonad ()
addConstraint c (mbName,ref) = do
     vars <- tc_vars <$> get
     case M.lookup ref vars of
       (Just (SVConstrained cs)) -> modify (\s -> s {tc_vars = M.insert ref (SVConstrained $ insConstraint c cs) vars})
       Nothing -> modify (\s -> s {tc_vars = M.insert ref (SVConstrained $ S.singleton c) vars})
       _ -> throwError $ "attempt to add constraint to rigid type" ++ show c ++ ", " ++ show (mbName, ref)
    where
      insConstraint c cs = S.insert c cs --make me smarter!


{-
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
    go vars (JTRecord xs) =
        JTRecord . M.fromList <$> mapM (\(n,t) -> (\x->(n,x)) <$> go vars t) (M.toList xs)
    go _ x = return x
-}

-- Manipulating the environment

withLocalScope :: TMonad a -> TMonad (a, Set Int)
withLocalScope act = do
  modify (\s -> s {tc_env   = M.empty : tc_env s,
                   tc_stack = S.empty : tc_stack s})
  res <- act
  frame <- head . tc_stack <$> get
  modify (\s -> s {tc_env   = drop 1 $ tc_env s,
                   tc_stack = drop 1 $ tc_stack s})
  return (res, frame)

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

--add mutation
resolveType :: JType -> TMonad JType
resolveType x = composOpM go x
    where
      go :: JType -> TMonad JType
      go x@(JTFree (mbName, ref)) = do
        vars <- tc_vars <$> get
        case M.lookup ref vars of
          Just (SVType t) -> go t
          _ -> return x
      go x = composOpM go x

--add mutation
resolveTypeShallow :: JType -> TMonad JType
resolveTypeShallow x = go x
    where
      go :: JType -> TMonad JType
      go x@(JTFree (mbName, ref)) = do
        vars <- tc_vars <$> get
        case M.lookup ref vars of
          Just (SVType t) -> go t
          _ -> return x
      go x = return x

integrateLocalType :: JType -> TMonad JType
integrateLocalType x = evalStateT (composOpM go x) M.empty
    where
      go :: JType -> StateT (Map Int JType) TMonad JType
      go (JTFree (mbName, ref)) = do
            m <- get
            case M.lookup ref m of
              Just newTy -> return newTy
              Nothing -> do
                (_,r) <- lift $ newVarRef
                let newTy = JTFree (mbName, r)
                put $ M.insert ref newTy m
                return newTy
      go x = composOpM go x

lookupEnv :: Ident -> TMonad JType
lookupEnv ident = resolveType =<< go . tc_env =<< get
    where go (e:es) = case M.lookup ident e of
                        Just t -> return t
                        Nothing -> go es
          go _ = tyErr1 "unable to resolve variable name: " ident



resolveConstraints :: Set Int -> TMonad ()
resolveConstraints vrs = undefined --mapM (resolveConstraint vrs S.empty) $ S.toList vrs

{-
resolveConstraint :: Set Int -> Set Int -> Int -> TMonad ()
resolveConstraint resolvable seen i = do --check vs seen, resolvable
     mbCs <- lookupConstraints (Nothing, i)
     case mbCs of
       Just cs -> do
                 cs' <- mapM simplifyConstraint cs
       Nothing -> return ()
  where
    simplifyConstraint (Sub t) = Sub <$> resolveConstrainedType t
    simplifyConstraint (Super t) = Super <$> resolveConstrainedType t
    simplifyConstraint (GLB s) = GLB . S.fromList <$> mapM resolveConstrainedType (S.toList s)
    simplifyConstraint (LUB s) = LUB . S.fromList <$> mapM resolveConstrainedType (S.toList s)

    resolveConstrainedType (JTFree vref) = undefined
-}

{-
data JType = JTNum
           | JTString
           | JTBool
           | JTStat
           | JTFunc [JType] (JType)
           | JTList JType --default case is tuple, type sig for list. tuples with <>
           | JTMap  JType
           | JTRecord VarRef [(String, JType)]
           | JTFree VarRef
             deriving (Eq, Ord, Read, Show, Typeable, Data)

data Constraint = Sub JType
                | Super JType
                | Choice Constraint Constraint
                | GLB (Set JType)
                | LUB (Set JType)
                  deriving (Eq, Ord, Show)

-}




-- Note, we can use this in place of integrateLocalType too...
-- should it really instantiate the result too, or not?
-- should we keep a list of schema vars? -- A: yes
instantiateSchema :: [JType] -> TMonad [JType]
instantiateSchema xs = evalStateT (mapM (composOpM go) xs) M.empty
    where
      go :: JType -> StateT (Map Int JType) TMonad JType
      go (JTFree vr@(mbName, ref)) = do
            m <- get
            case M.lookup ref m of
              Just newTy -> return newTy
              Nothing -> do
                (_,r) <- lift $ newVarRef
                let newRef = (mbName, r)
                let newTy = JTFree newRef
                put $ M.insert ref newTy m

                mbCs <- lift $ lookupConstraints vr
                case mbCs of
                  Just cs ->
                      mapM_ (\c -> lift $ addConstraint c newRef)  =<< mapM instantiateConstraint (S.toList cs)
                  Nothing -> return ()

                return newTy
      go x = composOpM go x

      lrt x = lift $ resolveType x

      instantiateConstraint (Sub t) = Sub <$> (go <=< lrt) t
      instantiateConstraint (Super t) = Sub <$> (go <=< lrt) t
      instantiateConstraint (GLB ts) = (GLB . S.fromList) <$> mapM (go <=< lrt) (S.toList ts)
      instantiateConstraint (LUB ts) = (LUB . S.fromList) <$> mapM (go <=< lrt) (S.toList ts)
      instantiateConstraint (Choice t1 t2) = (Choice <$> instantiateConstraint t1) `ap` instantiateConstraint t2



-- Subtyping

--here we resolve shallowly on evry recursive call because
--instantiation is possible
(<:) :: JType -> JType -> TMonad ()
x <: y = do
     xt <- resolveTypeShallow x
     yt <- resolveTypeShallow y
     if xt == yt
        then return ()
        else go xt yt
  where
    go xt@(JTFree ref) yt@(JTFree ref2) = addConstraint (Sub yt) ref >>
                                          addConstraint (Super xt) ref2
    go (JTFree ref) yt = addConstraint (Sub yt) ref
    go xt (JTFree ref) = addConstraint (Super xt) ref
    go xt@(JTFunc argsx retx) yt@(JTFunc argsy rety) = do
           when (length argsy < length argsx) $ tyErr2 "Couldn't subtype" xt yt
           zipWithM_ (<:) argsy argsx -- functions are contravariant in argument type
           retx <: rety -- functions are covariant in return type
    go (JTList xt) (JTList yt) = xt <: yt
    go (JTMap xt) (JTMap yt) = xt <: yt
    go (JTRecord xm) (JTRecord ym)
        | ym `M.isProperSubmapOf` xm =
            T.sequence (M.intersectionWith (<:) xm ym) >> return ()
    go xt yt = tyErr2 "Couldn't subtype" xt yt

--greatest lower bound
-- glb {a:Num} {b:Num} = {a:Num,b:Num}
x \/ y = do
     xt <- resolveType x
     yt <- resolveType y
     if xt == yt
       then return xt
       else go xt yt
  where
    go xt@(JTFree _) yt = do
           ret <- newVarRef
           addConstraint (GLB (S.fromList [xt,yt])) ret
           return (JTFree ret)
    go xt yt@(JTFree _) = go yt xt
    go xt@(JTFunc argsx retx) yt@(JTFunc argsy rety) =
           JTFunc <$> zipWithM (/\) argsx argsy <*> go retx rety
    go (JTList xt) (JTList yt) = JTList <$> go xt yt
    go (JTMap xt) (JTMap yt) = JTMap <$> go xt yt
    go (JTRecord xm) (JTRecord ym) =
        JTRecord <$> T.sequence (M.unionWith (\xt yt -> join $ liftM2 go xt yt) (M.map return xm) (M.map return ym))
    go xt yt
        | xt == yt = return xt
        | otherwise = return JTImpossible

--this can be optimized. split out the free vars, glb the rest, then return a single glb set
glball :: [JType] -> TMonad JType
glball (h:xs) = do
  foldM (\x y -> x \/ y) h xs
glball [] = return JTImpossible

--least upper bound
--lub {a:Num} {a:Num,b:Int} = {a:Num}
x /\ y = do
     xt <- resolveType x
     yt <- resolveType y
     if xt == yt
       then return xt
       else go xt yt
  where
    go xt@(JTFree _) yt = do
           ret <- newVarRef
           addConstraint (LUB (S.fromList [xt,yt])) ret
           return (JTFree ret)
    go xt yt@(JTFree _) = go yt xt
    go xt@(JTFunc argsx retx) yt@(JTFunc argsy rety) =
           JTFunc <$> zipWithOrIdM (\/) argsx argsy <*> go retx rety
    go (JTList xt) (JTList yt) = JTList <$> go xt yt
    go (JTMap xt) (JTMap yt) = JTMap <$> go xt yt
    go (JTRecord xm) (JTRecord ym) = do
        JTRecord <$> T.sequence (M.intersectionWith go xm ym)
    go xt yt
        | xt == yt = return xt
        | otherwise = return JTStat

--this can be optimized. split out the free vars, lub the rest, then return a single lub set
luball :: [JType] -> TMonad JType
luball (h:xs) = do
  foldM (\x y -> x /\ y) h xs
luball [] = return JTStat

--have a maybe version that checks for the free cases



instance JTypeCheck JExpr where
    typecheck (ValExpr e) = typecheck e
    typecheck (SelExpr e (StrI i)) =
        do et <- typecheck e
           case et of
             (JTRecord m) -> case M.lookup i m of
                               Just res -> return res
                               Nothing -> tyErr1 ("Record contains no field named " ++ show i) et -- record extension would go here
             (JTFree r) -> do
                            res <- newTyVar
                            addConstraint (Sub (JTRecord (M.singleton i res))) r
                            return res
             _ -> tyErr1 "Cannot use record selector on this value" et
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

    typecheck (PostExpr _ e) = case e of
                                 (SelExpr _ _) -> go
                                 (ValExpr (JVar _)) -> go
                                 (IdxExpr _ _) -> go
                                 _ -> tyErr1 "Value not compatible with postfix assignment" =<< typecheck e
        where go = ((<: JTNum) =<< typecheck e) >> return JTNum

    typecheck (IfExpr e e1 e2) = do
                            (<: JTBool) =<< typecheck e
                            t1 <- typecheck e1
                            t2 <- typecheck e2
                            t1 /\ t2

    typecheck (NewExpr e) = undefined --yipe
    typecheck (ApplExpr e appArgse) = do
                            et <- typecheck e
                            appArgst <- mapM typecheck appArgse
                            case et of
                              (JTFunc argst rett) -> do
                                        when (length argst > length appArgst) $ tyErr2l "Mismatched argument lengths" argst appArgst
                                        (rett':argst') <- instantiateSchema (rett:argst)
                                        zipWithM (<:) appArgst argst'
                                        return rett'
                              (JTFree _) -> do
                                        ret <- newTyVar
                                        et <: JTFunc appArgst ret
                                        return ret
                              _ -> tyErr1 "Cannot apply value as function" et


    typecheck (UnsatExpr _) = undefined --saturate (avoiding creation of existing ids) then typecheck
    typecheck (AntiExpr s) = fail $ "Antiquoted expression not provided with explicit signature: " ++ show s
    typecheck (TypeExpr forceType e t)
              | forceType = integrateLocalType t
              | otherwise = do
                            t2 <- typecheck e
                            t1 <- integrateLocalType t
                            t2 <: t1
                            return t1

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
    typecheck (JList xs) = fmap JTList . luball =<< mapM typecheck xs
    typecheck (JRegEx _) = undefined --regex object
    typecheck (JHash mp) = JTRecord . M.fromList <$> mapM go (M.toList mp)
        where go (n,v) = (\x -> (n,x)) <$> typecheck v
    typecheck (JFunc args body) = do
                           (t, frame) <- withLocalScope $ do
                                           argst <- mapM newVarDecl args
                                           res <- typecheck body
                                           return $ JTFunc argst res
                           resolveConstraints $ frame `S.difference` freeVars res
                           --we can still simplify freeVars of res, think about how...
                           --is there anything left to merge, or just let it sit?

-- undefined --bring args into scope as constrained vars, typecheck body, typecheck args, return function + frame of all things to clone
    typecheck (UnsatVal _) = undefined --saturate (avoiding creation of existing ids) then typecheck

instance JTypeCheck JStat where
    typecheck (DeclStat ident) = newVarDecl ident >> return JTStat
    typecheck (ReturnStat e) = typecheck e
    typecheck (IfStat e s s1) = do
                            (<: JTBool) =<< typecheck e
                            t <- typecheck s
                            t1 <- typecheck s1
                            t /\ t1
    typecheck (WhileStat e s) = do
                            (<: JTBool) =<< typecheck e
                            typecheck s
    typecheck (ForInStat _ _ _ _) = undefined -- yipe!
    typecheck (SwitchStat e xs d) = undefined -- check e, unify e with firsts, check seconds, take glb of seconds
                                    --oh, hey, add typecase to language!?
    typecheck (TryStat _ _ _ _) = undefined -- should be easy
    typecheck (BlockStat xs) = do
                            ts <- mapM typecheck xs
                            luball $ stripStat ts
        where stripStat (JTStat:ts) = stripStat ts
              stripStat (t:ts) = t : stripStat ts
              stripStat t = t
    typecheck (ApplStat args body) = typecheck (ApplExpr args body) >> return JTStat
    typecheck (PostStat s e) = typecheck (PostExpr s e) >> return JTStat
    typecheck (AssignStat e e1) = do
                            t <- typecheck e
                            t1 <- typecheck e1
                            t1 <: t
                            return JTStat
    typecheck (UnsatBlock _) = undefined --oyvey
    typecheck (AntiStat _) = undefined --oyvey
    typecheck BreakStat = return JTStat
    typecheck (ForeignStat i t) = integrateLocalType t >>= addEnv i >> return JTStat


{-
data JType = JTNum
           | JTString
           | JTBool
           | JTStat
           | JTFunc [JType] (JType)
           | JTList JType --default case is tuple, type sig for list. tuples with <>
           | JTMap  JType
           | JTRecord VarRef [(String, JType)]
           | JTFree VarRef
             deriving (Eq, Ord, Read, Show, Typeable, Data)
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
-}
