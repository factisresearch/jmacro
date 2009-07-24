{-# LANGUAGE FlexibleInstances, UndecidableInstances, OverlappingInstances, TypeFamilies, RankNTypes, DeriveDataTypeable, StandaloneDeriving, FlexibleContexts #-}

-----------------------------------------------------------------------------
{- |
Module      :  Language.Javascript.JMacro.Base
Copyright   :  (c) Gershom Bazerman, 2009
License     :  BSD 3 Clause
Maintainer  :  gershomb@gmail.com
Stability   :  experimental

Simple DSL for lightweight (untyped) programmatic generation of Javascript.
-}
-----------------------------------------------------------------------------

module Language.Javascript.JMacro.Base (
  -- * ADT
  JStat(..), JExpr(..), JVal(..), Ident(..),
  -- * Generic traversal (via compos)
  JMacro(..), MultiComp(..), Compos(..),
  composOp, composOpM, composOpM_, composOpFold,
  -- * Hygienic transformation
  withHygiene,
  -- * Display/Output
  renderJs, JsToDoc(..),
  -- * ad-hoc data marshalling
  ToJExpr(..),
  -- * helpful combinators
  jLam, jVar, jFor, jForIn, jForEachIn,
  expr2stat, ToStat(..), nullStat,
  -- * hash combinators
  jhEmpty, jhSingle, jhAdd, jhFromList,
  -- * utility
  jsSaturate
  ) where
import Prelude hiding (tail, init, head, last, minimum, maximum, foldr1, foldl1, (!!), read)
import Control.Applicative hiding (empty)
import Data.Function
import qualified Data.Map as M
import Text.PrettyPrint.HughesPJ
import Control.Monad.State.Strict
import Safe
import Control.Monad.Identity
import Data.Generics

{--------------------------------------------------------------------
  ADTs
--------------------------------------------------------------------}

--switch
--Yield statement?
--destructuring/pattern matching functions --pattern matching in lambdas.
--array comprehensions/generators?
--add postfix stat

-- | Statements
data JStat = DeclStat   Ident
           | ReturnStat JExpr
           | IfStat     JExpr JStat JStat
           | WhileStat  JExpr JStat
           | ForInStat  Bool Ident JExpr JStat
           | SwitchStat JExpr [(JExpr, JStat)] JStat
           | BlockStat  [JStat]
           | ApplStat   JExpr [JExpr]
           | PostStat   String JExpr
           | AssignStat JExpr JExpr
           | UnsatBlock (State [Ident] JStat)
           | AntiStat   String
           | BreakStat
             deriving (Eq, Ord, Show, Data, Typeable)

-- | Expressions
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

-- | Values
data JVal = JVar     Ident
          | JList    [JExpr]
          | JDouble  Double
          | JInt     Integer
          | JStr     String
          | JRegEx   String
          | JHash    (M.Map String JExpr)
          | JFunc    [Ident] JStat
          | UnsatVal (State [Ident] JVal)
            deriving (Eq, Ord, Show, Data, Typeable)

-- | Identifiers
newtype Ident = StrI String deriving (Eq, Ord, Show, Data, Typeable)


deriving instance Typeable2 State
deriving instance Data (State [Ident] JVal)
deriving instance Data (State [Ident] JExpr)
deriving instance Data (State [Ident] JStat)



expr2stat :: JExpr -> JStat
expr2stat (ApplExpr x y) = (ApplStat x y)
expr2stat (IfExpr x y z) = IfStat x (expr2stat y) (expr2stat z)
expr2stat (PostExpr s x) = PostStat s x
expr2stat (AntiExpr x) = AntiStat x
expr2stat _ = nullStat

{--------------------------------------------------------------------
  Compos
--------------------------------------------------------------------}

-- | Utility class to coerce the ADT into a regular structure.
class JMacro a where
    toMC :: a -> MultiComp
    fromMC :: MultiComp -> a

-- | Union type to allow regular traversal by compos.
data MultiComp = MStat JStat | MExpr JExpr | MVal JVal | MIdent Ident deriving Show


-- | Compos and ops for generic traversal as defined over
-- the JMacro ADT.
class Compos t where
    compos :: (forall a. a -> m a) -> (forall a b. m (a -> b) -> m a -> m b)
           -> (t -> m t) -> t -> m t


composOp :: Compos t => (t -> t) -> t -> t
composOp f = runIdentity . composOpM (Identity . f)
composOpM :: (Compos t, Monad m) => (t -> m t) -> t -> m t
composOpM = compos return ap
composOpM_ :: (Compos t, Monad m) => (t -> m ()) -> t -> m ()
composOpM_ = composOpFold (return ()) (>>)
composOpFold :: Compos t => b -> (b -> b -> b) -> (t -> b) -> t -> b
composOpFold z c f = unC . compos (\_ -> C z) (\(C x) (C y) -> C (c x y)) (C . f)
newtype C b a = C { unC :: b }



instance JMacro Ident where
    toMC = MIdent
    fromMC (MIdent x) = x
    fromMC _ = error "fromMC"

instance JMacro JVal where
    toMC = MVal
    fromMC (MVal x) = x
    fromMC _ = error "fromMC"

instance JMacro JExpr where
    toMC = MExpr
    fromMC (MExpr x) = x
    fromMC _ = error "fromMC"

instance JMacro JStat where
    toMC = MStat
    fromMC (MStat x) = x
    fromMC _ = error "fromMC"

instance JMacro [JStat] where
    toMC = MStat . BlockStat
    fromMC (MStat (BlockStat x)) = x
    fromMC _ = error "fromMC"

instance Compos MultiComp where
    compos ret app f' v = case v of
        MIdent _ -> ret v
        MStat v' -> ret MStat `app` case v' of
           DeclStat i -> ret DeclStat `app` f i
           ReturnStat i -> ret ReturnStat `app` f i
           IfStat e s s' -> ret IfStat `app` f e `app` f s `app` f s'
           WhileStat e s -> ret WhileStat `app` f e `app` f s
           ForInStat b i e s -> ret (ForInStat b) `app` f i `app` f e `app` f s
           SwitchStat e l d -> ret SwitchStat `app` f e `app` l' `app` f d
               where l' = mapM' (\(c,s) -> ret (,) `app` f c `app` f s) l
           BlockStat xs -> ret BlockStat `app` mapM' f xs
           ApplStat  e xs -> ret ApplStat `app` f e `app` mapM' f xs
           PostStat o e -> ret (PostStat o) `app` f e
           AssignStat e e' -> ret AssignStat `app` f e `app` f e'
           UnsatBlock _ -> ret v'
           AntiStat _ -> ret v'
           BreakStat -> ret BreakStat
        MExpr v' -> ret MExpr `app` case v' of
           ValExpr e -> ret ValExpr `app` f e
           SelExpr e e' -> ret SelExpr `app` f e `app` f e'
           IdxExpr e e' -> ret IdxExpr `app` f e `app` f e'
           InfixExpr o e e' -> ret (InfixExpr o) `app` f e `app` f e'
           PostExpr o e -> ret (PostExpr o) `app` f e
           IfExpr e e' e'' -> ret IfExpr `app` f e `app` f e' `app` f e''
           NewExpr e -> ret NewExpr `app` f e
           ApplExpr e xs -> ret ApplExpr `app` f e `app` mapM' f xs
           AntiExpr _ -> ret v'
           UnsatExpr _ -> ret v'
        MVal v' -> ret MVal `app` case v' of
           JVar i -> ret JVar `app` f i
           JList xs -> ret JList `app` mapM' f xs
           JDouble _ -> ret v'
           JInt    _ -> ret v'
           JStr    _ -> ret v'
           JRegEx  _ -> ret v'
           JHash   m -> ret JHash `app` m'
               where (ls, vs) = unzip (M.toList m)
                     m' = ret (M.fromAscList . zip ls) `app` mapM' f vs
           JFunc xs s -> ret JFunc `app` mapM' f xs `app` f s
           UnsatVal _ -> ret v'
      where
        mapM' g = foldr (app . app (ret (:)) . g) (ret [])
        f x = ret fromMC `app` f' (toMC x)


{--------------------------------------------------------------------
  New Identifiers
--------------------------------------------------------------------}

sat_ :: State [Ident] a -> a
sat_ x = evalState x $ newIdentSupply (Just "<<unsatId>>")

instance Eq a => Eq (State [Ident] a) where
    (==) = (==) `on` sat_
instance Ord a => Ord (State [Ident] a) where
    compare = compare `on` sat_
instance Show a => Show (State [Ident] a) where
    show x = "(" ++ show (sat_ x) ++ ")"

class ToSat a where
    toSat_ :: a -> [Ident] -> State [Ident] (JStat, [Ident])

instance ToSat [JStat] where
    toSat_ f vs = return $ (BlockStat f, reverse vs)

instance ToSat JStat where
    toSat_ f vs = return $ (f, reverse vs)

instance ToSat JExpr where
    toSat_ f vs = return $ (expr2stat f, reverse vs)

instance ToSat [JExpr] where
    toSat_ f vs = return $ (BlockStat $ map expr2stat f, reverse vs)

instance (ToSat a, b ~ JExpr) => ToSat (b -> a) where
    toSat_ f vs = do
      x <- takeOne
      toSat_ (f (ValExpr $ JVar x)) (x:vs)

takeOne :: (Monad m, MonadState [b] m) => m b
takeOne = do
  (x:xs) <- get
  put xs
  return x

newIdentSupply :: Maybe String -> [Ident]
newIdentSupply Nothing     = newIdentSupply (Just "jmId")
newIdentSupply (Just pfx') = [StrI (pfx ++ show x) | x <- [(0::Integer)..]]
    where pfx = pfx'++['_']

{-
splitIdentSupply :: ([Ident] -> ([Ident], [Ident]))
splitIdentSupply is = (takeAlt is, takeAlt (drop 1 is))
    where takeAlt (x:_:xs) = x : takeAlt xs
          takeAlt _ = error "splitIdentSupply: stream is not infinite"
-}

{--------------------------------------------------------------------
  Saturation
--------------------------------------------------------------------}

jsSaturate :: (JMacro a) => Maybe String -> a -> a
jsSaturate str x = evalState (jsSaturate_ x) (newIdentSupply str)

jsSaturate_ :: (JMacro a) => a -> State [Ident] a
jsSaturate_ e = fromMC <$> go (toMC e)
    where go v = case v of
                   MStat (UnsatBlock us) -> composOpM go =<< (MStat <$> us)
                   MExpr (UnsatExpr  us) -> composOpM go =<< (MExpr <$> us)
                   MVal  (UnsatVal   us) -> composOpM go =<< (MVal  <$> us)
                   _ -> composOpM go v

{--------------------------------------------------------------------
  Transformation
--------------------------------------------------------------------}

--doesn't apply to unsaturated bits
jsReplace_ :: JMacro a => [(Ident, Ident)] -> a -> a
jsReplace_ xs e = fromMC $ composOp go (toMC e)
    where go v = case v of
                   MIdent i -> maybe v MIdent (M.lookup i mp)
                   _ -> composOp go v
          mp = M.fromList xs

--only works on fully saturated things
jsUnsat_ :: JMacro a => [Ident] -> a -> State [Ident] a
jsUnsat_ xs e = do
  (idents,is') <- splitAt (length xs) <$> get
  put is'
  return $ jsReplace_ (zip xs idents) e

-- | Apply a transformation to a fully saturated syntax tree,
-- taking care to return any free variables back to their free state
-- following the transformation. As the transformation preserves
-- free variables, it is hygienic.
withHygiene:: JMacro a => (a -> a) -> a -> a
withHygiene f x = fromMC $ case mx of
              MStat _  -> toMC $ UnsatBlock (coerceMC <$> jsUnsat_ is' x'')
              MExpr _  -> toMC $ UnsatExpr  (coerceMC <$> jsUnsat_ is' x'')
              MVal  _  -> toMC $ UnsatVal   (coerceMC <$> jsUnsat_ is' x'')
              MIdent _ -> toMC $ f x
    where (x', (StrI l:_)) = runState (jsSaturate_ x) is
          x'' = f x'
          is = newIdentSupply (Just "inSat")
          lastVal = readNote "inSat" (drop 6 l) :: Int
          is' = take lastVal is
          mx = toMC x
          coerceMC :: (JMacro a, JMacro b) => a -> b
          coerceMC = fromMC . toMC

{-
jsReplace :: JMacro a => [(Ident, Ident)] -> a -> a
jsReplace xs = withHygiene (jsReplace_ xs)
-}

{--------------------------------------------------------------------
  Pretty Printing
--------------------------------------------------------------------}

-- | Render a syntax tree as a pretty-printable document
-- (simply showing the resultant doc produces a nice,
-- well formatted String).
renderJs :: (JsToDoc a, JMacro a) => a -> Doc
renderJs = jsToDoc . jsSaturate Nothing

braceNest :: Doc -> Doc
braceNest x = char '{' $$ nest 2 x $$ char '}'

braceNest' :: Doc -> Doc
braceNest' x = char '{' $+$ nest 2 x $$ char '}'

class JsToDoc a
    where jsToDoc :: a -> Doc

instance JsToDoc JStat where
    jsToDoc (IfStat cond x y) = text "if" <> parens (jsToDoc cond) $$ braceNest' (jsToDoc x) $$ mbElse
        where mbElse | y == BlockStat []  = empty
                     | otherwise = text "else" $$ braceNest' (jsToDoc y)
    jsToDoc (DeclStat x) = text "var" <+> jsToDoc x
    jsToDoc (WhileStat p b)  = text "while" <> parens (jsToDoc p) $$ braceNest' (jsToDoc b)
    jsToDoc (UnsatBlock e) = jsToDoc $ sat_ e
    jsToDoc BreakStat = text "break"
    jsToDoc (ForInStat each i e b) = text txt <> parens (text "var" <+> jsToDoc i <+> text "in" <+> jsToDoc e) $$ braceNest' (jsToDoc b)
        where txt | each = "for each"
                  | otherwise = "for"
    jsToDoc (SwitchStat e l d) = text "switch" <+> parens (jsToDoc e) $$ braceNest' cases
        where l' = map (\(c,s) -> text "case" <+> parens (jsToDoc c) <> char ':' $$ nest 2 (jsToDoc [s])) l ++ [text "default:" $$ nest 2 (jsToDoc [d])]
              cases = vcat l'
    jsToDoc (ReturnStat e) = text "return" <+> jsToDoc e
    jsToDoc (ApplStat e es) = jsToDoc e <> (parens . fsep . punctuate comma $ map jsToDoc es)
    jsToDoc (AssignStat i x) = jsToDoc i <+> char '=' <+> jsToDoc x
    jsToDoc (PostStat op x) = jsToDoc x <> text op
    jsToDoc (AntiStat s) = text $ "`(" ++ s ++ ")`"
    jsToDoc (BlockStat xs) = jsToDoc (flattenBlocks xs)
        where flattenBlocks (BlockStat y:ys) = flattenBlocks y ++ flattenBlocks ys
              flattenBlocks (y:ys) = y : flattenBlocks ys
              flattenBlocks [] = []

instance JsToDoc JExpr where
    jsToDoc (ValExpr x) = jsToDoc x
    jsToDoc (SelExpr x y) = cat [jsToDoc x <> char '.', jsToDoc y]
    jsToDoc (IdxExpr x y) = jsToDoc x <> brackets (jsToDoc y)
    jsToDoc (IfExpr x y z) = parens (jsToDoc x <+> char '?' <+> jsToDoc y <+> char ':' <+> jsToDoc z)
    jsToDoc (InfixExpr op x y) = parens $ sep [jsToDoc x, text op, jsToDoc y]
    jsToDoc (PostExpr op x) = jsToDoc x <> text op
    jsToDoc (ApplExpr je xs) = jsToDoc je <> (parens . fsep . punctuate comma $ map jsToDoc xs)
    jsToDoc (NewExpr e) = text "new" <+> jsToDoc e
    jsToDoc (AntiExpr s) = text $ "`(" ++ s ++ ")`"
    jsToDoc (UnsatExpr e) = jsToDoc $ sat_ e

instance JsToDoc JVal where
    jsToDoc (JVar i) = jsToDoc i
    jsToDoc (JList xs) = brackets . fsep . punctuate comma $ map jsToDoc xs
    jsToDoc (JDouble d) = double d
    jsToDoc (JInt i) = integer i
    jsToDoc (JStr s) = text ("\""++s++"\"")
    jsToDoc (JRegEx s) = text ("/"++s++"/")
    jsToDoc (JHash m) = braceNest . fsep . punctuate comma . map (\(x,y) -> quotes (text x) <> colon <+> jsToDoc y) $ M.toList m
    jsToDoc (JFunc is b) = parens $ text "function" <> parens (fsep . punctuate comma . map jsToDoc $ is) $$ braceNest' (jsToDoc b)
    jsToDoc (UnsatVal f) = jsToDoc $ sat_ f

instance JsToDoc Ident where
    jsToDoc (StrI s) = text s

instance JsToDoc [JExpr] where
    jsToDoc = vcat . map ((<> semi) . jsToDoc)

instance JsToDoc [JStat] where
    jsToDoc = vcat . map ((<> semi) . jsToDoc)

{--------------------------------------------------------------------
  ToJExpr Class
--------------------------------------------------------------------}

-- | Things that can be marshalled into javascript values.
-- Instantiate for any necessary data structures.
class ToJExpr a where
    toJExpr :: a -> JExpr
    toJExprFromList :: [a] -> JExpr
    toJExprFromList = ValExpr . JList . map toJExpr

instance ToJExpr a => ToJExpr [a] where
    toJExpr = toJExprFromList

instance ToJExpr JExpr where
    toJExpr = id

instance ToJExpr () where
    toJExpr _ = ValExpr $ JList []

instance ToJExpr Bool where
    toJExpr True  = jsv "true"
    toJExpr False = jsv "false"

instance ToJExpr JVal where
    toJExpr = ValExpr

instance ToJExpr a => ToJExpr (M.Map String a) where
    toJExpr = ValExpr . JHash . M.map toJExpr

instance ToJExpr Double where
    toJExpr = ValExpr . JDouble

instance ToJExpr Int where
    toJExpr = ValExpr . JInt . fromIntegral

instance ToJExpr Integer where
    toJExpr = ValExpr . JInt

instance ToJExpr Char where
    toJExpr = ValExpr . JStr . (:[])
    toJExprFromList = ValExpr . JStr . escQuotes
        where escQuotes = tailDef "" . initDef "" . show

instance (ToJExpr a, ToJExpr b) => ToJExpr (a,b) where
    toJExpr (a,b) = ValExpr . JList $ [toJExpr a, toJExpr b]

instance (ToJExpr a, ToJExpr b, ToJExpr c) => ToJExpr (a,b,c) where
    toJExpr (a,b,c) = ValExpr . JList $ [toJExpr a, toJExpr b, toJExpr c]

instance (ToJExpr a, ToJExpr b, ToJExpr c, ToJExpr d) => ToJExpr (a,b,c,d) where
    toJExpr (a,b,c,d) = ValExpr . JList $ [toJExpr a, toJExpr b, toJExpr c, toJExpr d]
instance (ToJExpr a, ToJExpr b, ToJExpr c, ToJExpr d, ToJExpr e) => ToJExpr (a,b,c,d,e) where
    toJExpr (a,b,c,d,e) = ValExpr . JList $ [toJExpr a, toJExpr b, toJExpr c, toJExpr d, toJExpr e]
instance (ToJExpr a, ToJExpr b, ToJExpr c, ToJExpr d, ToJExpr e, ToJExpr f) => ToJExpr (a,b,c,d,e,f) where
    toJExpr (a,b,c,d,e,f) = ValExpr . JList $ [toJExpr a, toJExpr b, toJExpr c, toJExpr d, toJExpr e, toJExpr f]

instance Num JExpr where
    fromInteger = ValExpr . JInt . fromIntegral
    x + y = InfixExpr "+" x y
    x - y = InfixExpr "-" x y
    x * y = InfixExpr "*" x y
    abs x = ApplExpr (jsv "Math.abs") [x]
    signum x = IfExpr (InfixExpr ">" x 0) 1 (IfExpr (InfixExpr "==" x 0) 0 (-1))

{--------------------------------------------------------------------
  Block Sugar
--------------------------------------------------------------------}

class ToStat a where
    toStat :: a -> JStat

instance ToStat JStat where
    toStat = id

instance ToStat [JStat] where
    toStat = BlockStat

instance ToStat JExpr where
    toStat = expr2stat

instance ToStat [JExpr] where
    toStat = BlockStat . map expr2stat

{--------------------------------------------------------------------
  Combinators
--------------------------------------------------------------------}

-- | Create a new anonymous function. The result is an expression.
-- Usage:
-- @jLam $ \ x y -> {JExpr involving x and y}@
jLam :: (ToSat a) => a -> JExpr
jLam f = ValExpr . UnsatVal $ do
           (block,is) <- toSat_ f []
           return $ JFunc is block

-- | Introduce a new variable into scope for the duration
-- of the enclosed expression. The result is a block statement.
-- Usage:
-- @jVar $ \ x y -> {JExpr involving x and y}@
jVar :: (ToSat a) => a -> JStat
jVar f = UnsatBlock $ do
           (block, is) <- toSat_ f []
           let addDecls (BlockStat ss) =
                  BlockStat $ map DeclStat is ++ ss
               addDecls x = x
           return $ addDecls block

-- | Create a \"for in\" statement.
-- Usage:
-- @jForIn {expression} $ \x -> {block involving x}
jForIn :: ToSat a => JExpr -> (JExpr -> a) -> JStat
jForIn e f = UnsatBlock $ do
               (block, is) <- toSat_ f []
               return $ ForInStat False (headNote "jForIn" is) e block

-- | As with "jForIn" but creating a \"for each in\" statement.
jForEachIn :: ToSat a => JExpr -> (JExpr -> a) -> JStat
jForEachIn e f = UnsatBlock $ do
               (block, is) <- toSat_ f []
               return $ ForInStat True (headNote "jForIn" is) e block

jsv :: String -> JExpr
jsv = ValExpr . JVar . StrI

jFor :: (ToJExpr a, ToStat b) => JStat -> a -> JStat -> b -> JStat
jFor before p after b = BlockStat [before, WhileStat (toJExpr p) b']
    where b' = case toStat b of
                 BlockStat xs -> BlockStat $ xs ++ [after]
                 x -> BlockStat [x,after]

jhEmpty :: M.Map String JExpr
jhEmpty = M.empty

jhSingle :: ToJExpr a => String -> a -> M.Map String JExpr
jhSingle k v = jhAdd k v $ jhEmpty

jhAdd :: ToJExpr a => String -> a -> M.Map String JExpr -> M.Map String JExpr
jhAdd  k v m = M.insert k (toJExpr v) m

jhFromList :: [(String, JExpr)] -> JVal
jhFromList = JHash . M.fromList

nullStat :: JStat
nullStat = BlockStat []