{-# Language StandaloneDeriving, DeriveDataTypeable, FlexibleContexts, UndecidableInstances, FlexibleInstances #-}
module Language.Javascript.JMacro.Types (
  JType(..), anyType, parseType, runTypeParser, VarRef
  ) where

import Control.Applicative hiding ((<|>))
import Data.Char

import Data.Maybe(fromJust)

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Error
import Text.Parsec.Prim hiding (runParser)
import Text.ParserCombinators.Parsec.Language(emptyDef)
import qualified Text.ParserCombinators.Parsec.Token as P

import qualified Data.Set as S
import qualified Data.Map as M
import Data.Map (Map)
import Data.Generics
import Data.Typeable

type VarRef = (Maybe String, Int)

-- sum types for list/record, map/record

data JType = JTNum
           | JTString
           | JTBool
           | JTStat
           | JTFunc [JType] (JType)
           | JTList JType
           | JTMap  JType
           | JTRecord (Map String JType)
           | JTImpossible
           | JTFree VarRef
             deriving (Eq, Ord, Read, Show, Typeable, Data)


type TypeParserState = (Int, Map String Int)

typLang :: P.LanguageDef TypeParserState
typLang = emptyDef {
           P.reservedNames = ["()","->"],
           P.reservedOpNames = ["()","->","::"],
           P.identLetter = alphaNum <|> oneOf "_$",
           P.identStart  = letter <|> oneOf "_$"
          }

lexer = P.makeTokenParser typLang

whiteSpace= P.whiteSpace lexer
symbol    = P.symbol lexer
parens    = P.parens lexer
braces    = P.braces lexer
brackets  = P.brackets lexer
dot       = P.dot lexer
colon     = P.colon lexer
semi      = P.semi lexer
identifier= P.identifier lexer
reserved  = P.reserved lexer
reservedOp= P.reservedOp lexer
commaSep1 = P.commaSep1 lexer
commaSep  = P.commaSep  lexer

lexeme    = P.lexeme lexer

parseType :: String -> Either ParseError JType
parseType s = runParser anyType (0,M.empty) "" s

runTypeParser = withLocalState (0,M.empty) anyType

withLocalState :: st -> CharParser st a -> CharParser st' a
withLocalState initState subParser = mkPT $ \s@(State input pos otherState) -> do
  res <- runParsecT subParser (State input pos initState)
  return $ fixState otherState res
      where
        fixState s res = (fmap . fmap) go res
            where go (Ok a (State input pos _localState) pe) = Ok a (State input pos s) pe
                  go (Error e) = (Error e)

type TypeParser a = CharParser TypeParserState a

nullType = reservedOp "()" >> return JTStat

atomicType :: TypeParser JType
atomicType = do
  a <- identifier
  case a of
    "Num" -> return JTNum
    "String" -> return JTString
    "Bool" -> return JTBool
    (x:xs) | isUpper x -> fail $ "Unknown type: " ++ a
           | otherwise -> freeVar a
    _ -> error "typeAtom"

funOrAtomType :: TypeParser JType
funOrAtomType = do
  r <- anyNestedType `sepBy1` (lexeme (string "->"))
  return $ case r of
    [x] -> x
    (x:xs) -> JTFunc (init r) (last r)
    _ -> error "funOrAtomType"

listType :: TypeParser JType
listType = JTList <$> brackets anyType

anyType :: TypeParser JType
anyType = nullType <|> parens anyType <|> funOrAtomType <|> listType <|> recordType

anyNestedType :: TypeParser JType
anyNestedType = nullType <|> parens anyType <|> atomicType <|> listType <|> recordType

recordType :: TypeParser JType
recordType = braces $ JTRecord . M.fromList <$> commaSep namePair
    where namePair = do
            n <- identifier
            reservedOp "::"
            t <- anyType
            return (n, t)

freeVar :: String -> TypeParser JType
freeVar v = do
  (i,m) <- getState
  JTFree . (\x -> (Just v, x)) <$> maybe (setState (i+1,M.insert v i m) >> return i)
             return
             (M.lookup v m)


