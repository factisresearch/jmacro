{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, PatternGuards #-}

module Language.Javascript.JMacro.TypeCheck where

import Language.Javascript.JMacro.Base
import Language.Javascript.JMacro.Types
import Language.Javascript.JMacro.QQ

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Error
import Data.Map (Map)
import Data.List(intercalate, nub, partition)
import Data.Traversable hiding (sequence, mapM)
import qualified Data.Traversable as T
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S

import Text.PrettyPrint.HughesPJ

import Debug.Trace

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

partitionOut :: (a -> Maybe b) -> [a] -> ([b],[a])
partitionOut f xs' = foldr go ([],[]) xs'
    where go x ~(bs,as)
             | Just b <- f x = (b:bs,as)
             | otherwise = (bs,x:as)

zipWithOrChange :: (a -> a -> b) -> (a -> b) -> [a] -> [a] -> [b]
zipWithOrChange f g xss yss = go xss yss
    where go (x:xs) (y:ys) = f x y : go xs ys
          go xs@(_:_) _ = map g xs
          go _ ys = map g ys

zipWithOrIdM :: Monad m => (a -> a -> m a) -> [a] -> [a] -> m [a]
zipWithOrIdM f xs ys = sequence $ zipWithOrChange f return xs ys

unionWithM :: (Monad m, Ord key) => (val -> val -> m val) -> Map key val -> Map key val -> m (Map key val)
unionWithM f m1 m2 = T.sequence $ M.unionWith (\xm ym -> join $ liftM2 f xm ym) (M.map return m1) (M.map return m2)

intersectionWithM :: (Monad m, Ord key) => (val -> val -> m b) -> Map key val -> Map key val -> m (Map key b)
intersectionWithM f m1 m2 = T.sequence $ M.intersectionWith f m1 m2

--constraints can be resolved if you can't assign to a value any further, which is the same as if you generalize.

-- Basic Types and TMonad

data StoreVal = SVType JType
              | SVConstrained (Set Constraint)
                deriving Show

data TCState = TCS {tc_env :: [Map Ident JType],
                    tc_vars :: Map Int StoreVal,
                    tc_stack :: [Set Int],
                    tc_resolvable :: Set Int,
                    tc_varCt :: Int} deriving Show

tcStateEmpty = TCS [M.empty] M.empty [S.empty] S.empty 0

newtype TMonad a = TMonad (ErrorT String (State TCState) a) deriving (Functor, Monad, MonadState TCState, MonadError String, Applicative)

instance Applicative (ErrorT String (State TCState)) where
    pure = return
    (<*>) = ap

class JTypeCheck a where
    typecheck :: a -> TMonad JType

evalTMonad (TMonad x) = evalState (runErrorT x) tcStateEmpty

runTMonad (TMonad x) = runState (runErrorT x) tcStateEmpty

-- Output prettyPrinters
class PrettyType a where
    prettyType :: a -> TMonad String

--assums x is resolved
freeVarsWithNames :: JType -> TMonad (Map Int String)
freeVarsWithNames x = do
  fmap (either id int2Name) . fst <$> execStateT (go x) (M.empty, 0)
    where
      go :: JType -> StateT (Map Int (Either String Int), Int) TMonad ()
      go t@(JTFree (mbName, ref)) = do
                        (m,ct) <- get
                        case M.lookup ref m of
                          Just (Left _) -> return ()
                          Just (Right _) -> case mbName of
                                              Just name -> put (M.insert ref (Left name) m, ct)
                                              Nothing -> return ()
                          Nothing -> do
                               put (M.insert ref (Right ct) m, ct + 1)
                               mapM_ (go . fromC) =<< lift (lookupConstraintsList (mbName, ref))
      go x = composOpM_ go x

      fromC (Sub t) = t
      fromC (Super t) = t

      int2Name i
          | q == 0 = [letter]
          | otherwise = letter : show q
          where (q,r) = divMod i 26
                letter = toEnum (fromEnum 'a' + r) :: Char

instance PrettyType JType where
    prettyType x = do
        xt <- resolveType x
        names <- freeVarsWithNames xt
        let xt' = replaceNames names xt
        constraintStrings <- nub . concat <$> mapM (prettyConstraints names) (M.keys names)
        let typStr = show $ jsToDoc $ replaceNames names xt
        let constraintStr
                | null constraintStrings = ""
                | otherwise = "(" ++ intercalate ", " constraintStrings ++ ") => "
        return $ constraintStr ++ typStr
      where
        replaceNames names (JTFree (_,ref)) = JTFree (M.lookup ref names,ref)
        replaceNames names v = composOp (replaceNames names) v

        prettyConstraints names ref =
          map prettyConstraint <$> lookupConstraintsList (Nothing, ref)
            where
              myName = case M.lookup ref names of
                         Just n -> n
                         Nothing -> "t_"++show ref
              prettyConstraint (Sub x) = myName ++ " <: " ++ (show $ jsToDoc $ replaceNames names x)
              prettyConstraint (Super x) = (show $ jsToDoc $ replaceNames names x) ++ " <: " ++ myName

tyErr0 :: String -> TMonad a
tyErr0 x = throwError x

tyErr1 :: PrettyType a => String -> a -> TMonad b
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

prettyEnv :: TMonad [Map Ident String]
prettyEnv = do
  env <- tc_env <$> get
  mapM (T.mapM prettyType) env

runTypecheckFull x = runTMonad $ do
                       r <- typecheck x
                       e <- prettyEnv
                       return (r,e)

runTypecheck x = evalTMonad . typecheck $ x


evalTypecheck x = evalTMonad $ do
                    typecheck x
                    e <- prettyEnv
                    return e

-- Manipulating VarRefs and Constraints
newVarRef :: TMonad VarRef
newVarRef = do
  v <- tc_varCt <$> get
  modify (\s -> s {tc_varCt = v + 1,
                   tc_stack = addStack v (tc_stack s)})
  return $ (Nothing, v)
      where addStack v (s:ss) = S.insert v s : ss
            addStack v _ = error "newVarRef: no sets" --[S.singleton v]

newTyVar :: TMonad JType
newTyVar = JTFree <$> newVarRef

mapConstraint :: (Monad m, Functor m) => (JType -> m JType) -> Constraint -> m Constraint
mapConstraint f (Sub t) = Sub <$> f t
mapConstraint f (Super t) = Super <$> f t

--add mutation
lookupConstraintsList :: VarRef -> TMonad [Constraint]
lookupConstraintsList (_,ref) = do
  vars <- tc_vars <$> get
  case M.lookup ref vars of
    (Just (SVConstrained cs)) -> mapM (mapConstraint resolveType) (S.toList cs)
    (Just (SVType t)) -> tyErr1 "lookupConstraints on instantiated type" t
    _ -> return []

--note, when checking constraints don't actually need to add new ones
--because, in theory, the contrarywise ones already exist
--on the other hand this could force cascading instantiations, which is good.
instantiateVarRef :: VarRef -> JType -> TMonad ()
instantiateVarRef vr@(_,ref) t = do
    cs <- lookupConstraintsList vr
    modify (\s -> s {tc_vars = M.insert ref (SVType t) (tc_vars s)})
    checkConstraints t cs

checkConstraints :: JType -> [Constraint] -> TMonad ()
checkConstraints t cs = mapM_ go cs
    where go (Sub t2) = t <: t2
          go (Super t2) = t2 <: t

addConstraint :: VarRef -> Constraint -> TMonad ()
addConstraint vr@(mbName,ref) c = case c of
       Sub t -> case t of
                  JTFree _ -> addC c

                  JTFunc args res -> do
                         args' <- mapM (const newTyVar) args
                         res'  <- newTyVar
                         zipWithM (<:) args args' --contravariance
                         res' <: res
                         instantiateVarRef vr $ JTFunc args' res'

                  JTRecord m -> do
                         (ms,restCs) <- findRecordSubs <$> lookupConstraintsList vr
                         t' <- JTRecord <$> foldM (unionWithM (\x y -> someLowerBound [x,y])) m ms
                         putCs (S.fromList $ Sub t' : restCs)

                  JTList t -> do
                         vr' <- newVarRef
                         addConstraint vr' (Sub t)
                         instantiateVarRef vr (JTList (JTFree vr'))

                  JTMap t -> do
                         vr' <- newVarRef
                         addConstraint vr' (Sub t)
                         instantiateVarRef vr (JTMap (JTFree vr'))

                  _ -> do
                         instantiateVarRef vr t

       Super t -> case t of
                  JTFree _ -> addC c

                  JTFunc args res -> do
                         args' <- mapM (const newTyVar) args
                         res'  <- newTyVar
                         zipWithM (<:) args' args --contravariance
                         res <: res'
                         instantiateVarRef vr $ JTFunc args' res'

                  JTRecord m -> do
                         (ms,restCs) <- findRecordSups <$> lookupConstraintsList vr
                         t' <- JTRecord <$> foldM (intersectionWithM (\x y -> someUpperBound [x,y])) m ms
                         putCs (S.fromList $ Super t' : restCs)

                  JTList t -> do
                         vr' <- newVarRef
                         addConstraint vr' (Super t)
                         instantiateVarRef vr (JTList (JTFree vr'))

                  JTMap t -> do
                         vr' <- newVarRef
                         addConstraint vr' (Super t)
                         instantiateVarRef vr (JTMap (JTFree vr'))

                  _ -> do
                         instantiateVarRef vr t
    where
      putCs cs =
        modify (\s -> s {tc_vars = M.insert ref (SVConstrained cs) (tc_vars s)})

      addC constraint = do
        cs <- lookupConstraintsList vr
        modify (\s -> s {tc_vars = M.insert ref (SVConstrained (S.fromList $ constraint:cs)) (tc_vars s)})

      findRecordSubs cs = partitionOut go cs
          where go (Sub (JTRecord m)) = Just m
                go _ = Nothing

      findRecordSups cs = partitionOut go cs
          where go (Super (JTRecord m)) = Just m
                go _ = Nothing

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
    (e:es) -> modify (\s -> s {tc_env = M.insert ident typ e : es}) -- we clobber/shadow var names
    _ -> throwError "empty env stack (this should never happen)"

newVarDecl :: Ident -> TMonad JType
newVarDecl ident = do
  v <- newTyVar
  addEnv ident v
  return v

resolveTypeGen :: ((JType -> TMonad JType) -> JType -> TMonad JType)
               -> JType
               -> TMonad JType
resolveTypeGen f x = go x
    where
      go :: JType -> TMonad JType
      go x@(JTFree (mbName, ref)) = do
        vars <- tc_vars <$> get
        case M.lookup ref vars of
          Just (SVType t) -> do
            res <- go t
            -- mutation to shortcut pointer chasing
            when (res /= t) $ modify (\s -> s {tc_vars = M.insert ref (SVType res) $ tc_vars s})
            return res
          _ -> return x
      go x = f go x

resolveType = resolveTypeGen composOpM
resolveTypeShallow = resolveTypeGen (const return)

{-
--mk these the same
--add mutation
resolveType :: JType -> TMonad JType
resolveType x = go x
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
-}

integrateLocalType :: JLocalType -> TMonad JType
integrateLocalType (env,t) = evalStateT (go t) M.empty
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
          go _ = tyErr0 $ "unable to resolve variable name: " ++ (show $ jsToDoc $ ident)

freeVars :: JType -> TMonad (Set Int)
freeVars x = do
  x' <- resolveType x
  execWriterT (go x')
    where
      go :: JType -> WriterT (Set Int) TMonad ()
      go t@(JTFree (_, ref)) = tell (S.singleton ref)
      go x = composOpM_ go x

{-
resolveConstraints :: Set Int -> TMonad ()
resolveConstraints vrs = mapM_ (resolveConstraint vrs S.empty) $ S.toList vrs

resolveConstraint :: Set Int -> Set Int -> Int -> TMonad ()
resolveConstraint resolvable seen i
    | i `S.member` seen = error "loop" -- not really
    | i `S.member` resolvable = do
             cs <- lookupConstraints (Nothing, i)
             cs' <- mapM reduceConstraint $ S.toList cs
             --now either resolve or error or set
             return ()
    | otherwise = return ()
  where
    reduceConstraint (Sub t) = Sub <$> (resolveConstrainedType <=< resolveType) t
    reduceConstraint (Super t) = Super <$> (resolveConstrainedType <=< resolveType) t
--    reduceConstraint (GLB s) = GLB . S.fromList <$> mapM (resolveConstrainedType <=< resolveType) (S.toList s)
--    reduceConstraint (LUB s) = LUB . S.fromList <$> mapM (resolveConstrainedType <=< resolveType) (S.toList s)

    resolveConstrainedType x = go x
        where go t@(JTFree _) = do
                t' <- resolveType t
                case t' of
                  (JTFree (_,v)) -> do
                                  resolveConstraint resolvable (S.insert i seen) v
                                  resolveType t'
                  _ -> composOpM go t'
              go x = composOpM go x
--func
--record
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
instantiateSchema xs = evalStateT (mapM go xs) M.empty
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

                mapM_ (lift . addConstraint newRef <=< mapConstraint go) =<< lift (lookupConstraintsList vr)

                return newTy
      go x = composOpM go x



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
    go _ JTStat = return ()
    go xt@(JTFree ref) yt@(JTFree ref2) = addConstraint ref  (Sub yt) >>
                                          addConstraint ref2 (Super xt)
    go (JTFree ref) yt = addConstraint ref (Sub yt)
    go xt (JTFree ref) = addConstraint ref (Super xt)
    go xt@(JTFunc argsx retx) yt@(JTFunc argsy rety) = do
           when (length argsy < length argsx) $ tyErr2 "Couldn't subtype" xt yt
           zipWithM_ (<:) argsy argsx -- functions are contravariant in argument type
           retx <: rety -- functions are covariant in return type
    go (JTList xt) (JTList yt) = xt <: yt
    go (JTMap xt) (JTMap yt) = xt <: yt
    go (JTRecord xm) (JTRecord ym)
        | ym `M.isProperSubmapOf` xm = intersectionWithM (<:) xm ym >> return ()
    go xt yt = tyErr2 "Couldn't subtype" xt yt

--have a maybe version that checks for the free cases

someUpperBound :: [JType] -> TMonad JType
someUpperBound xs = do
  res <- newTyVar
  mapM (<: res) xs
  return res

someLowerBound :: [JType] -> TMonad JType
someLowerBound xs = do
  res <- newTyVar
  mapM (res <:) xs
  return res


x =.= y = do
      x <: y
      y <: x
      return x

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
                            addConstraint r (Sub (JTRecord (M.singleton i res)))
                            return res
             _ -> tyErr1 "Cannot use record selector on this value" et
    typecheck (IdxExpr e e1) = undefined --this is tricky
    typecheck (InfixExpr s e e1)
        | s `elem` ["-","/","*"] = setFixed JTNum >> return JTNum
        | s == "+" = setFixed JTNum >> return JTNum -- `orElse` setFixed JTStr --TODO: Intersection types
        | s `elem` [">","<"] = setFixed JTNum >> return JTBool
        | s `elem` ["==","/="] = do
                            et <- typecheck e
                            e1t <- typecheck e1
                            et =.= e1t
                   -- equality means typechecking subtypes in both directions
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
                            someUpperBound [t1,t2] --t1 /\ t2

    typecheck (NewExpr e) = undefined --yipe

    typecheck (ApplExpr e appArgse) = do
                            et <- typecheck e
                            appArgst <- mapM typecheck appArgse
                            case et of
                              (JTFunc argst rett) -> do
                                        (rett':argst') <- instantiateSchema (rett:argst)
                                        zipWithM_ (<:) (appArgst ++ repeat JTStat) argst'
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
    typecheck (JList xs) = fmap JTList . someUpperBound =<< mapM typecheck xs
    typecheck (JRegEx _) = undefined --regex object
    typecheck (JHash mp) = JTRecord . M.fromList <$> mapM go (M.toList mp)
        where go (n,v) = (\x -> (n,x)) <$> typecheck v
    typecheck (JFunc args body) = do
                           ((argst',res'), frame) <- withLocalScope $ do
                                           argst <- mapM newVarDecl args
                                           res <- typecheck body
                                           return (argst,res)
                           resolveType $ JTFunc argst' res'
--                           free <- freeVars res'
--                           resolveConstraints $ frame `S.difference` free
--                           resolveType $ JTFunc argst' res'


                           --we can still simplify freeVars of res, think about how...

                           --is there anything left to merge, or just let it sit?

    typecheck (UnsatVal _) = undefined --saturate (avoiding creation of existing ids) then typecheck

instance JTypeCheck JStat where
    typecheck (DeclStat ident) = newVarDecl ident >> return JTStat
    typecheck (ReturnStat e) = typecheck e
    typecheck (IfStat e s s1) = do
                            (<: JTBool) =<< typecheck e
                            t <- typecheck s
                            t1 <- typecheck s1
                            someUpperBound [t,t1] --t /\ t1
    typecheck (WhileStat e s) = do
                            (<: JTBool) =<< typecheck e
                            typecheck s
    typecheck (ForInStat _ _ _ _) = undefined -- yipe!
    typecheck (SwitchStat e xs d) = undefined -- check e, unify e with firsts, check seconds, take glb of seconds
                                    --oh, hey, add typecase to language!?
    typecheck (TryStat _ _ _ _) = undefined -- should be easy
    typecheck (BlockStat xs) = do
                            ts <- mapM typecheckWithBlock xs
                            someUpperBound $ stripStat ts
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


typecheckWithBlock stat = typecheck stat `catchError` \ e -> throwError $ e ++ "\nIn statement:\n" ++ renderStyle (style {mode = OneLineMode}) (renderJs stat)
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

{-
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
           addConstraint ret (GLB (S.fromList [xt,yt]))
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
           addConstraint ret (LUB (S.fromList [xt,yt]))
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
-}
