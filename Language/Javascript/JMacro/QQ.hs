{-# LANGUAGE FlexibleInstances, UndecidableInstances, OverlappingInstances, TemplateHaskell, QuasiQuotes #-}

-----------------------------------------------------------------------------
{- |
Module      :  Language.Javascript.JMacro
Copyright   :  (c) Gershom Bazerman, 2009
License     :  BSD 3 Clause
Maintainer  :  gershomb@gmail.com
Stability   :  experimental

Simple EDSL for lightweight (untyped) programmatic generation of Javascript.
-}
-----------------------------------------------------------------------------

module Language.Javascript.JMacro.QQ(jmacro,jmacroE) where
import Prelude hiding (tail, init, head, last, minimum, maximum, foldr1, foldl1, (!!), read)
import Control.Applicative hiding ((<|>),many,optional,(<*))
import Control.Arrow((&&&))
import Control.Monad.State.Strict
import qualified Data.ByteString.Char8 as BS
import Data.Char(digitToInt, toLower)
import Data.List(isPrefixOf, sort)
import Data.Generics(extQ,Data)
import qualified Data.Map as M

import Language.Haskell.Meta.Parse
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH(mkName)
import qualified Language.Haskell.TH.Lib as TH
import Language.Haskell.TH.Quote

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Pos
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language(javaStyle)

import Text.Regex.PCRE.Light (compileM)

import Language.Javascript.JMacro.Base

-- import Debug.Trace

--compileM _ _ = Right "hack"

{--------------------------------------------------------------------
  QuasiQuotation
--------------------------------------------------------------------}

-- | QuasiQuoter for a block of JMacro statements.
jmacro :: QuasiQuoter
jmacro = QuasiQuoter quoteJMExp quoteJMPat

-- | QuasiQuoter for a JMacro expression.
jmacroE :: QuasiQuoter
jmacroE = QuasiQuoter quoteJMExpE quoteJMPatE

quoteJMPat :: String -> TH.PatQ
quoteJMPat s = case parseJM s of
               Right x -> dataToPatQ (const Nothing) x
               Left err -> fail (show err)

quoteJMExp :: String -> TH.ExpQ
quoteJMExp s = do
    (f,p) <- (TH.loc_filename &&& TH.loc_start) <$> TH.location
    case parseJMPos s f p of
               Right x -> jm2th x
               Left err -> fail (show err)

quoteJMPatE :: String -> TH.PatQ
quoteJMPatE s = case parseJME s of
               Right x -> dataToPatQ (const Nothing) x
               Left err -> fail (show err)

quoteJMExpE :: String -> TH.ExpQ
quoteJMExpE s = do
    (f,p) <- (TH.loc_filename &&& TH.loc_start) <$> TH.location
    case parseJMEPos s f p of
               Right x -> jm2th x
               Left err -> fail (show err)

-- | Traverse a syntax tree, replace an identifier by an
-- antiquotation of a free variable.
-- Don't replace identifiers on the right hand side of selector
-- expressions.
antiIdent :: JMacro a => String -> a -> a
antiIdent s e = fromMC $ go (toMC e)
    where go (MExpr (ValExpr (JVar (StrI s'))))
             | s == s' = MExpr (AntiExpr s)
          go (MExpr (SelExpr x i)) =
              MExpr (SelExpr (antiIdent s x) i)
          go x = composOp go x

antiIdents :: JMacro a => [String] -> a -> a
antiIdents ss x = foldr antiIdent x ss


jm2th :: Data a => a -> TH.ExpQ
jm2th v = dataToExpQ (const Nothing
                      `extQ` handleStat
                      `extQ` handleExpr
                      `extQ` handleVal
                     ) v

    where handleStat :: JStat -> Maybe (TH.ExpQ)
          handleStat (BlockStat ss) = Just $
                                      appConstr "BlockStat" $
                                      TH.listE (blocks ss)
              where blocks :: [JStat] -> [TH.ExpQ]
                    blocks [] = []

                    blocks (DeclStat (StrI i):xs) = case i of
                     ('!':i') -> jm2th (DeclStat (StrI i')) : blocks xs
                     _ ->
                        [TH.appE (TH.varE $ mkName "jVar")
                              (TH.lamE [TH.varP . mkName $ i] $
                                 appConstr "BlockStat"
                                 (TH.listE $ blocks $ map (antiIdent i) xs))]

                    blocks (x:xs) = jm2th x : blocks xs
          handleStat (ForInStat b (StrI i) e s) = Just $
                 appFun (TH.varE $ forFunc)
                        [jm2th e,
                         TH.lamE [TH.varP $ mkName i]
                                 (jm2th $ antiIdent i s)
                         ]
              where forFunc
                        | b = mkName "jForEachIn"
                        | otherwise = mkName "jForIn"
          handleStat (AntiStat s) = case parseExp s of
                                      Right ans -> Just $ TH.appE (TH.varE (mkName "toStat"))
                                                                  (return ans)
                                      Left err -> Just $ fail err
          handleStat _ = Nothing

          handleExpr :: JExpr -> Maybe (TH.ExpQ)
          handleExpr (AntiExpr s) = case parseExp s of
                                      Right ans -> Just $ TH.appE (TH.varE (mkName "toJExpr")) (return ans)
                                      Left err -> Just $ fail err
          handleExpr (ValExpr (JFunc is' s)) = Just $
              TH.appE (TH.varE $ mkName "jLam")
                      (TH.lamE (map (TH.varP . mkName) is)
                               (jm2th $ antiIdents is s))
            where is = map (\(StrI i) -> i) is'

          handleExpr _ = Nothing

          handleVal :: JVal -> Maybe (TH.ExpQ)
          handleVal (JHash m) = Just $
                                TH.appE (TH.varE $ mkName "jhFromList") $
                                jm2th (M.toList m)
          handleVal _ = Nothing

          appFun x = foldl (TH.appE) x
          appConstr n = TH.appE (TH.conE $ mkName n)


{--------------------------------------------------------------------
  Parsing
--------------------------------------------------------------------}

type JMParser a =  CharParser () a

lexer :: P.TokenParser ()
symbol :: String -> JMParser String
parens, braces :: JMParser a -> JMParser a
dot, colon, semi, identifier, identifierWithBang :: JMParser String
whiteSpace :: JMParser ()
reserved, reservedOp :: String -> JMParser ()
commaSep, commaSep1 :: JMParser a -> JMParser [a]

lexer = P.makeTokenParser jsLang


jsLang :: P.LanguageDef ()
jsLang = javaStyle {
           P.reservedNames = ["var","return","if","else","while","for","in","break","new","function","switch","case","default","fun"],
           P.reservedOpNames = ["--","*","/","+","-",".","?","=","==","!=","<",">","&&","||","++","===",">=","<=","->"],
           P.identLetter = alphaNum <|> oneOf "_$",
           P.identStart  = letter <|> oneOf "_$",
           P.commentLine = "//",
           P.commentStart = "/*",
           P.commentEnd = "*/"}

identifierWithBang = P.identifier $ P.makeTokenParser $ jsLang {P.identStart = letter <|> oneOf "_$!"}

whiteSpace= P.whiteSpace lexer
symbol    = P.symbol lexer
parens    = P.parens lexer
braces    = P.braces lexer
-- brackets  = P.brackets lexer
dot       = P.dot lexer
colon     = P.colon lexer
semi      = P.semi lexer
identifier= P.identifier lexer
reserved  = P.reserved lexer
reservedOp= P.reservedOp lexer
commaSep1 = P.commaSep1 lexer
commaSep  = P.commaSep  lexer

lexeme :: JMParser a -> JMParser a
lexeme    = P.lexeme lexer

(<*) :: Monad m => m b -> m a -> m b
x <* y = do
  xr <- x
  y
  return xr

parseJMPos :: String -> String -> (Int, Int) -> Either ParseError JStat
parseJMPos s f (p1,p2) = BlockStat <$> runParser jmacroParser () "" s
    where jmacroParser = do
            setPosition $ newPos f p1 p2
            ans <- statblock
            eof
            return ans

parseJM :: String -> Either ParseError JStat
parseJM s = BlockStat <$> runParser jmacroParser () "" s
    where jmacroParser = do
            ans <- statblock
            eof
            return ans

parseJME :: String -> Either ParseError JExpr
parseJME s = runParser jmacroParserE () "" s
    where jmacroParserE = do
            ans <- whiteSpace >> expr
            eof
            return ans

parseJMEPos :: String -> String -> (Int, Int) -> Either ParseError JExpr
parseJMEPos s f (p1,p2) = runParser jmacroParserE () "" s
    where jmacroParserE = do
            setPosition $ newPos f p1 p2
            ans <- whiteSpace >> expr
            eof
            return ans

{-
ident :: JMParser Ident
ident = do
  i <- identifier
  when ("jmId_" `isPrefixOf` i) $ fail "Illegal use of reserved jmId_ prefix in variable name."
  return (StrI i)
-}

varidentdecl :: JMParser Ident
varidentdecl = do
  i <- identifierWithBang
  when ("jmId_" `isPrefixOf` i || "!jmId_" `isPrefixOf` i) $ fail "Illegal use of reserved jmId_ prefix in variable name."
  when (i=="this" || i=="!this") $ fail "Illegal attempt to name variable 'this'."
  return (StrI i)


identdecl :: JMParser Ident
identdecl = do
  i <- identifier
  when ("jmId_" `isPrefixOf` i) $ fail "Illegal use of reserved jmId_ prefix in variable name."
  when (i=="this") $ fail "Illegal attempt to name variable 'this'."
  return (StrI i)

identAssignDecl :: JMParser [JStat]
identAssignDecl = varidentdecl >>= \i ->
                  (do
                    reservedOp "="
                    e <- expr
                    return [DeclStat i, AssignStat (ValExpr (JVar (clean i))) e]
                  )
                  <|> return [DeclStat i]
    where clean (StrI ('!':x)) = StrI x
          clean x = x

statblock :: JMParser [JStat]
statblock = concat <$> (sepEndBy1 (whiteSpace >> statement) (semi <|> return ""))

l2s :: [JStat] -> JStat
l2s xs = BlockStat xs


-- return either an expression or a statement
statement :: JMParser [JStat]
statement = declStat
            <|> funDecl
            <|> functionDecl
            <|> returnStat
            <|> ifStat
            <|> whileStat
            <|> switchStat
            <|> forStat
            <|> braces statblock
            <|> assignStat
            <|> applStat
            <|> breakStat
            <|> antiStat
          <?> "statement"
    where
      declStat =
          reserved "var" >> concat <$> commaSep1 identAssignDecl
      -- take assignment

      functionDecl = do
        reserved "function"
        n <- varidentdecl
        as <- parens (commaSep identdecl) <|> many1 identdecl
        b <- try (ReturnStat <$> braces expr) <|> (l2s <$> statement)
        return $ [DeclStat n, AssignStat (ValExpr $ JVar (clean n)) (ValExpr $ JFunc as b)]
            where clean (StrI ('!':x)) = StrI x
                  clean x = x

      funDecl = do
        reserved "fun"
        n <- identdecl
        as <- many identdecl
        b <- try (ReturnStat <$> braces expr) <|> (l2s <$> statement) <|> (symbol "->" >> ReturnStat <$> expr)
        return $ [DeclStat (addBang n), AssignStat (ValExpr $ JVar n) (ValExpr $ JFunc as b)]
            where addBang (StrI x) = StrI ('!':x)

      returnStat =
        reserved "return" >> (:[]) . ReturnStat <$> expr

      ifStat = do
        reserved "if"
        p <- parens expr
        b <- l2s <$> statement
        isElse <- (lookAhead (reserved "else") >> return True)
                  <|> return False
        if isElse
          then do
            reserved "else"
            return . IfStat p b . l2s <$> statement
          else return $ [IfStat p b nullStat]

      whileStat =
          reserved "while" >> liftM2 (\e b -> [WhileStat e (l2s b)])
                              (parens expr) statement

      switchStat = do
        reserved "switch"
        e <- parens $ expr
        (l,d) <- braces (liftM2 (,) (many caseStat) (option ([]) dfltStat))
        return $ [SwitchStat e l (l2s d)]

      caseStat =
        reserved "case" >> liftM2 (,) expr (char ':' >> l2s <$> statblock)

      dfltStat =
        reserved "default:" >> statblock

      forStat =
        reserved "for" >> ((reserved "each" >> inBlock True)
                           <|> try (inBlock False)
                           <|> simpleForStat)

      inBlock isEach = do
        char '(' >> whiteSpace >> optional (reserved "var")
        i <- identdecl
        reserved "in"
        e <- expr
        char ')' >> whiteSpace
        s <- l2s <$> statement
        return $ [ForInStat isEach i e s]

      simpleForStat = do
        (before,after,p) <- parens threeStat
        b <- statement
        return $ jFor' before after p b
          where threeStat =
                    liftM3 (,,) (statement)
                                (semi >> expr)
                                (semi >> statement)
                jFor' :: (ToJExpr a) => [JStat] -> a -> [JStat] -> [JStat] -> [JStat]
                jFor' before p after bs = before ++ [WhileStat (toJExpr p) b']
                    where b' = BlockStat $ bs ++ after


      assignStat = do
          e1 <- try $ dotExpr <* reservedOp "="
          let gofail = fail ("Invalid assignment.")
          case e1 of
            ValExpr (JVar (StrI "this")) -> gofail
            ValExpr (JVar _) -> return ()
            ValExpr _ -> gofail
            _ -> return ()
          e2 <- expr
          return [AssignStat e1 e2]

      applStat = expr2stat' =<< expr

--fixme: don't handle ifstats
      expr2stat' e = case expr2stat e of
                       BlockStat [] -> pzero
                       x -> return [x]
{-
      expr2stat' :: JExpr -> JStat
      expr2stat' (ApplExpr x y) = return $ (ApplStat x y)
      expr2stat' (IfExpr x y z) = liftM2 (IfStat x) (expr2stat' y) (expr2stat' z)
      expr2stat' (PostExpr s x) = return $ PostStat s x
      expr2stat' (AntiExpr x)   = return $ AntiStat x
      expr2stat' _ = fail "Value expression used as statement"
-}

      breakStat = reserved "break" >> return [BreakStat]

      antiStat  = return . AntiStat <$> do
        x <- (try (symbol "`(") >> anyChar `manyTill` try (symbol ")`"))
        either (fail . ("Bad AntiQuotation: \n" ++))
               (const (return x))
               (parseExp x)

--args :: JMParser [JExpr]
--args = parens $ commaSep expr

expr :: JMParser JExpr
expr = do
    e <- expr'
    addIf e <|> return e
  where addIf e = do
          symbol "?"
          t <- expr
          colon
          el <- expr
          let ans = (IfExpr e t el)
          addIf ans <|> return ans

        expr' = buildExpressionParser table dotExpr <?> "expression"

        table = [[iop "*", iop "/"],
                 [iop "+", iop "-"],
                 [iope "==", iope "!=", iope "<", iope ">",
                  iope ">=", iope "<=", iope "==="],
                 [iop "&&", iop "||"]
                ]
        iop  s  = Infix (reservedOp s >> return (InfixExpr s)) AssocLeft
        iope s  = Infix (reservedOp s >> return (InfixExpr s)) AssocNone

dotExpr :: JMParser JExpr
dotExpr = do
  e <- many1 (lexeme dotExprOne) <?> "simple expression"
  case e of
    [e'] -> return e'
    (e':es) -> return $ ApplExpr e' es
    _ -> error "exprApp"

dotExprOne :: JMParser JExpr
dotExprOne = addNxt =<< valExpr <|> antiExpr <|> parens' expr <|> notExpr <|> newExpr
  where
    addNxt e = do
            nxt <- (Just <$> lookAhead anyChar <|> return Nothing)
            case nxt of
              Just '.' -> addNxt =<< (dot >> (SelExpr e <$> ident'))
              Just '[' -> addNxt =<< (IdxExpr e <$> brackets' expr)
              Just '(' -> addNxt =<< (ApplExpr e <$> args')
              Just '-' -> try (reservedOp "--" >> return (PostExpr "--" e)) <|> return e
              Just '+' -> try (reservedOp "++" >> return (PostExpr "++" e)) <|> return e
              _   -> return e

    notExpr = try (symbol "!" >> dotExpr) >>= \e ->
              return (ApplExpr (ValExpr (JVar (StrI "!"))) [e])

    newExpr = NewExpr <$> (reserved "new" >> dotExpr)

    antiExpr  = AntiExpr <$> do
         x <- (try (symbol "`(") >> anyChar `manyTill` try (string ")`"))
         either (fail . ("Bad AntiQuotation: \n" ++))
                (const (return x))
                (parseExp x)

    valExpr = ValExpr <$> (num <|> negnum <|> str <|> try regex <|> list <|> hash <|> func <|> var) <?> "value"
        where num = either JInt JDouble <$> try natFloat
              negnum = either (JInt . negate) (JDouble . negate) <$> try (char '-' >> natFloat)
              str   = JStr   <$> (myStringLiteral '"' <|> myStringLiteral '\'')
              regex = do
                s <- myRegexLiteral
                case compileM (BS.pack s) [] of
                  Right _ -> return (JRegEx s)
                  Left err -> fail ("Parse error in regexp: " ++ err)
              list  = JList  <$> brackets' (commaSep expr)
              hash  = JHash  . M.fromList <$> braces' (commaSep propPair)
              var = JVar <$> ident'
              func = do
                (symbol "\\" >> return ()) <|> reserved "function"
                liftM2 JFunc (parens (commaSep identdecl) <|> many identdecl)
                             (braces' statOrEblock <|>
                               (symbol "->" >> (ReturnStat <$> expr)))
              statOrEblock  = try (ReturnStat <$> expr `folBy` '}') <|> (l2s <$> statblock)
              propPair = liftM2 (,) myIdent (colon >> expr)

notFolBy a b = a <* notFollowedBy (char b)
folBy :: JMParser a -> Char -> JMParser a
folBy a b = a <* (lookAhead (char b) >>= const (return ()))
args' :: JMParser [JExpr]
args' = parens $ commaSep expr

--Parsers without Lexeme

braces', brackets', parens' :: JMParser a -> JMParser a
brackets' = around' '[' ']'
braces' = around' '{' '}'
parens' = around' '(' ')'

around' :: Char -> Char -> JMParser a -> JMParser a
around' a b x = lexeme (char a) >> (lexeme x <* char b)

myIdent :: JMParser String
myIdent = lexeme $ many1 (alphaNum <|> oneOf "_-!@#$%^&*();") <|> myStringLiteral '\''

ident' :: JMParser Ident
ident' = do
    i <- identifier'
    when ("jmId_" `isPrefixOf` i) $ fail "Illegal use of reserved jmId_ prefix in variable name."
    return (StrI i)
  where
    identifier' =
        try $
        do{ name <- ident''
          ; if isReservedName name
             then unexpected ("reserved word " ++ show name)
             else return name
          }
    ident''
        = do{ c <- P.identStart jsLang
            ; cs <- many (P.identLetter jsLang)
            ; return (c:cs)
            }
        <?> "identifier"
    isReservedName name
        = isReserved theReservedNames caseName
        where
          caseName      | P.caseSensitive jsLang  = name
                        | otherwise               = map toLower name
    isReserved names name
        = scan names
        where
          scan []       = False
          scan (r:rs)   = case (compare r name) of
                            LT  -> scan rs
                            EQ  -> True
                            GT  -> False
    theReservedNames
        | P.caseSensitive jsLang  = sortedNames
        | otherwise               = map (map toLower) sortedNames
        where
          sortedNames   = sort (P.reservedNames jsLang)


natFloat :: Fractional a => JMParser (Either Integer a)
natFloat = (char '0' >> zeroNumFloat)
           <|> decimalFloat <?> "number"
 where
    zeroNumFloat    =  (Left <$> (hexadecimal <|> octal))
                       <|> decimalFloat
                       <|> fractFloat 0
                       <|> return (Left 0)

    decimalFloat    = do n <- decimal
                         option (Left n)(fractFloat n)
    fractFloat n    = Right <$> fractExponent n
    fractExponent n = (do fract <- fraction
                          expo  <- option 1.0 exponent'
                          return ((fromInteger n + fract)*expo)
                      )
                      <|> ((fromInteger n *) <$> exponent')
    fraction        = char '.' >> (foldr op 0.0 <$> many1 digit <?> "fraction")
                    where
                      op d f    = (f + fromIntegral (digitToInt d))/10.0
    exponent'       = do oneOf "eE"
                         f <- sign
                         power . f <$> decimal
                    where
                       power e  | e < 0      = 1.0/power(-e)
                                | otherwise  = fromInteger (10^e)

    sign            =   (char '-' >> return negate)
                    <|> (char '+' >> return id)
                    <|> return id

    decimal         = number 10 digit
    hexadecimal     = oneOf "xX" >> number 16 hexDigit
    octal           = oneOf "oO" >> number 8 octDigit

    number base baseDig = foldl (\x d -> base*x + toInteger (digitToInt d)) 0 <$> many1 baseDig

myStringLiteral :: Char -> JMParser String
myStringLiteral t = do
    char t
    x <- concat <$> many myChar
    char t
    return x
 where myChar = do
         c <- noneOf [t]
         case c of
           '\\' -> do
                  c2 <- anyChar
                  return [c,c2]
           '\n' -> return "\\n"
           _ -> return [c]

myRegexLiteral :: JMParser String
myRegexLiteral = do
    char '/' `notFolBy` ' '
    x <- concat <$> many myChar
    char '/'
    return x
 where myChar = do
         c <- noneOf ['/']
         case c of
           '\\' -> do
                  c2 <- anyChar
                  return [c,c2]
           '\n' -> return "\\n"
           _ -> return [c]