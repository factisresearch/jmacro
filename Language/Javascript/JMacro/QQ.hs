{-# LANGUAGE FlexibleInstances, UndecidableInstances, OverlappingInstances, TypeFamilies, TemplateHaskell, QuasiQuotes #-}

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

module Language.Javascript.JMacro.QQ(jmacro,jmacroE,parseJM) where
import Prelude hiding (tail, init, head, last, minimum, maximum, foldr1, foldl1, (!!), read)
import Control.Applicative hiding ((<|>),many,optional,(<*))
import Control.Monad.State.Strict
import qualified Data.ByteString.Char8 as BS
import Data.Char(digitToInt, toLower, isUpper)
import Data.List(isPrefixOf, sort)
import Data.Generics(extQ,Data)
import qualified Data.Map as M

--import Language.Haskell.Meta.Parse
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH(mkName)
import qualified Language.Haskell.TH.Lib as TH
import Language.Haskell.TH.Quote

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Error
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language(javaStyle)

import Text.Regex.PCRE.Light (compileM)

import Language.Javascript.JMacro.Base
import Language.Javascript.JMacro.Types
import Language.Javascript.JMacro.ParseTH

import Debug.Trace

{--------------------------------------------------------------------
  QuasiQuotation
--------------------------------------------------------------------}

-- | QuasiQuoter for a block of JMacro statements.
jmacro :: QuasiQuoter
jmacro = QuasiQuoter {quoteExp = quoteJMExp, quotePat = quoteJMPat}

-- | QuasiQuoter for a JMacro expression.
jmacroE :: QuasiQuoter
jmacroE = QuasiQuoter {quoteExp = quoteJMExpE, quotePat = quoteJMPatE}

quoteJMPat :: String -> TH.PatQ
quoteJMPat s = case parseJM s of
               Right x -> dataToPatQ (const Nothing) x
               Left err -> fail (show err)

quoteJMExp :: String -> TH.ExpQ
quoteJMExp s = case parseJM s of
               Right x -> jm2th x
               Left err -> do
                   (line,_) <- TH.loc_start <$> TH.location
                   let pos = errorPos err
                   let newPos = setSourceLine pos $ line + sourceLine pos - 1
                   fail (show $ setErrorPos newPos err)

quoteJMPatE :: String -> TH.PatQ
quoteJMPatE s = case parseJME s of
               Right x -> dataToPatQ (const Nothing) x
               Left err -> fail (show err)

quoteJMExpE :: String -> TH.ExpQ
quoteJMExpE s = case parseJME s of
               Right x -> jm2th x
               Left err -> do
                   (line,_) <- TH.loc_start <$> TH.location
                   let pos = errorPos err
                   let newPos = setSourceLine pos $ line + sourceLine pos - 1
                   fail (show $ setErrorPos newPos err)


-- | Traverse a syntax tree, replace an identifier by an
-- antiquotation of a free variable.
-- Don't replace identifiers on the right hand side of selector
-- expressions.
antiIdent :: JMacro a => String -> a -> a
antiIdent s e = fromMC $ go (toMC e)
    where go (MExpr (ValExpr (JVar (StrI s'))))
             | s == s' = MExpr (AntiExpr $ fixIdent s)
          go (MExpr (SelExpr x i)) =
              MExpr (SelExpr (antiIdent s x) i)
          go x = composOp go x

antiIdents :: JMacro a => [String] -> a -> a
antiIdents ss x = foldr antiIdent x ss


fixIdent css@(c:_)
    | isUpper c = '_' : escapeDollar css
    | otherwise = escapeDollar css
  where
    escapeDollar = map (\x -> if x =='$' then 'ǆ' else x)
fixIdent _ = "_"


jm2th :: Data a => a -> TH.ExpQ
jm2th v = dataToExpQ (const Nothing
                      `extQ` handleStat
                      `extQ` handleExpr
                      `extQ` handleVal
                      `extQ` handleStr
                      `extQ` handleTyp
                     ) v

    where handleStat :: JStat -> Maybe (TH.ExpQ)
          handleStat (BlockStat ss) = Just $
                                      appConstr "BlockStat" $
                                      TH.listE (blocks ss)
              where blocks :: [JStat] -> [TH.ExpQ]
                    blocks [] = []
                    blocks (DeclStat (StrI i) t:xs) = case i of
                     ('!':'!':i') -> jm2th (DeclStat (StrI i') t) : blocks xs
                     ('!':i') ->
                        [TH.appE (TH.lamE [TH.varP . mkName . fixIdent $ i'] $
                                 appConstr "BlockStat"
                                 (TH.listE . (ds:) . blocks $ xs)) (TH.appE (TH.varE $ mkName "jsv")
                                                                            (TH.litE $ TH.StringL i'))]
                        where ds =
                                  TH.appE
                                        (TH.appE (TH.conE $ mkName "DeclStat")
                                               (TH.appE (TH.conE $ mkName "StrI")
                                                      (TH.litE $ TH.StringL i')))
                                        (jm2th t)
                     _ ->
                        [TH.appE
                           (TH.appE (TH.varE $ mkName "jVarTy")
                                  (TH.lamE [TH.varP . mkName . fixIdent $ i] $
                                     appConstr "BlockStat"
                                     (TH.listE $ blocks $ map (antiIdent i) xs)))
                           (jm2th t)
                        ]

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

          handleStat (TryStat s (StrI i) s1 s2)
              | s1 == BlockStat [] = Nothing
              | otherwise = Just $
                 appFun (TH.varE $ mkName "jTryCatchFinally")
                        [jm2th s,
                         TH.lamE [TH.varP $ mkName i]
                                 (jm2th $ antiIdent i s1),
                         jm2th s2
                         ]

          handleStat (AntiStat s) = case parseHSExp s of
                                      Right ans -> Just $ TH.appE (TH.varE (mkName "toStat"))
                                                                  (return ans)
                                      Left err -> Just $ fail err

          handleStat _ = Nothing

          handleExpr :: JExpr -> Maybe (TH.ExpQ)
          handleExpr (AntiExpr s) = case parseHSExp s of
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

          handleStr :: String -> Maybe (TH.ExpQ)
          handleStr x = Just $ TH.litE $ TH.StringL x

          handleTyp :: JType -> Maybe (TH.ExpQ)
          handleTyp (JTRecord t mp) = Just $
                                    TH.appE (TH.appE (TH.varE $ mkName "jtFromList") (jm2th t))
                                          (jm2th $ M.toList mp)

          handleTyp _ = Nothing

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
           P.reservedNames = ["var","return","if","else","while","for","in","break","new","function","switch","case","default","fun","try","catch","finally","foreign"],
           P.reservedOpNames = ["--","*","/","+","-",".","%","?","=","==","!=","<",">","&&","||","++","===",">=","<=","->","::","::!"],
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

{-
ident :: JMParser Ident
ident = do
  i <- identifier
  when ("jmId_" `isPrefixOf` i) $ fail "Illegal use of reserved jmId_ prefix in variable name."
  return (StrI i)
-}


getType = do
  isForce <- (reservedOp "::!" >> return True) <|> (reservedOp "::" >> return False)
  t <- runTypeParser
  return (isForce, t)

addForcedType (Just (True,t)) e = TypeExpr True e t
addForcedType _ e = e

--function !foo or function foo or var !x or var x, with optional type
varidentdecl :: JMParser (Ident, Maybe (Bool, JLocalType))
varidentdecl = do
  i <- identifierWithBang
  when ("jmId_" `isPrefixOf` i || "!jmId_" `isPrefixOf` i) $ fail "Illegal use of reserved jmId_ prefix in variable name."
  when (i=="this" || i=="!this") $ fail "Illegal attempt to name variable 'this'."
  t <- optionMaybe getType
  return (StrI i, t)

--any other identifier decl
identdecl :: JMParser Ident
identdecl = do
  i <- identifier
  when ("jmId_" `isPrefixOf` i) $ fail "Illegal use of reserved jmId_ prefix in variable name."
  when (i=="this") $ fail "Illegal attempt to name variable 'this'."
  return (StrI i)

--varidentdecls can take types!
identAssignDecl :: JMParser [JStat]
identAssignDecl = do
  (i,mbTyp) <- varidentdecl
  optAssignStat <- optionMaybe $ do
                    reservedOp "="
                    e <- expr
                    return $ AssignStat (ValExpr (JVar (clean i))) (addForcedType mbTyp e)
  return $ DeclStat i (fmap snd mbTyp) : maybe [] (:[]) optAssignStat
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
            <|> foreignStat
            <|> returnStat
            <|> ifStat
            <|> whileStat
            <|> switchStat
            <|> forStat
            <|> braces statblock
            <|> assignStat
            <|> tryStat
            <|> applStat
            <|> breakStat
            <|> antiStat
          <?> "statement"
    where
      declStat = do
        reserved "var"
        res <- concat <$> commaSep1 identAssignDecl
        _ <- semi
        return res

      functionDecl = do
        reserved "function"

        (i,mbTyp) <- varidentdecl
        as <- parens (commaSep identdecl) <|> many1 identdecl
        b <- try (ReturnStat <$> braces expr) <|> (l2s <$> statement)
        return $ [DeclStat i (fmap snd mbTyp),
                  AssignStat (ValExpr $ JVar (clean i)) (addForcedType mbTyp $ ValExpr $ JFunc as b)]
            where clean (StrI ('!':x)) = StrI x
                  clean x = x

      funDecl = do
        reserved "fun"
        n <- identdecl
        mbTyp <- optionMaybe getType
        as <- many identdecl
        b <- try (ReturnStat <$> braces expr) <|> (l2s <$> statement) <|> (symbol "->" >> ReturnStat <$> expr)
        return $ [DeclStat (addBang n) (fmap snd mbTyp),
                  AssignStat (ValExpr $ JVar n) (addForcedType mbTyp $ ValExpr $ JFunc as b)]

            where addBang (StrI x) = StrI ('!':'!':x)

      foreignStat = do
          reserved "foreign"
          i <- try $ identdecl <* reservedOp "::"
          t <- runTypeParser
          return [ForeignStat i t]

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

      tryStat = do
        reserved "try"
        s <- statement
        isCatch <- (lookAhead (reserved "catch") >> return True)
                  <|> return False
        (i,s1) <- if isCatch
                  then do
                    reserved "catch"
                    liftM2 (,) (parens identdecl) statement
                  else return $ (StrI "", [])
        isFinally <- (lookAhead (reserved "finally") >> return True)
                  <|> return False
        s2 <- if isFinally
                then reserved "finally" >> statement
                else return $ []
        return [TryStat (BlockStat s) i (BlockStat s1) (BlockStat s2)]


      dfltStat =
        reserved "default" >> char ':' >> whiteSpace >> statblock

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
                                (expr)
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
               (parseHSExp x)

--args :: JMParser [JExpr]
--args = parens $ commaSep expr

expr :: JMParser JExpr
expr = do
  e <- exprWithIf
  addType e
  where
    addType e = do
         optTyp <- optionMaybe getType
         case optTyp of
           (Just (b,t)) -> return $ TypeExpr b e t
           Nothing -> return e
    exprWithIf = do
         e <- rawExpr
         addIf e <|> return e
    addIf e = do
          reservedOp "?"
          t <- exprWithIf
          _ <- colon
          el <- exprWithIf
          let ans = (IfExpr e t el)
          addIf ans <|> return ans
    rawExpr = buildExpressionParser table dotExpr <?> "expression"
    table = [[iop "*", iop "/", iop "%"],
             [iop "++", iop "+", iop "-"],
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
              Just '.' -> addNxt =<< (dot >> (SelExpr e <$> (ident' <|> numIdent)))
              Just '[' -> addNxt =<< (IdxExpr e <$> brackets' expr)
              Just '(' -> addNxt =<< (ApplExpr e <$> args')
              Just '-' -> try (reservedOp "--" >> return (PostExpr "--" e)) <|> return e
              Just '+' -> try (reservedOp "++" >> return (PostExpr "++" e)) <|> return e
              _   -> return e

    numIdent = StrI <$> many1 digit

    notExpr = try (symbol "!" >> dotExpr) >>= \e ->
              return (ApplExpr (ValExpr (JVar (StrI "!"))) [e])

    newExpr = NewExpr <$> (reserved "new" >> dotExpr)

    antiExpr  = AntiExpr <$> do
         x <- (try (symbol "`(") >> anyChar `manyTill` try (string ")`"))
         either (fail . ("Bad AntiQuotation: \n" ++))
                (const (return x))
                (parseHSExp x)

    valExpr = ValExpr <$> (num <|> negnum <|> str <|> try regex <|> list <|> hash <|> func <|> var) <?> "value"
        where num = either JInt JDouble <$> try natFloat
              negnum = either (JInt . negate) (JDouble . negate) <$> try (char '-' >> natFloat)
              str   = JStr   <$> (myStringLiteral '"' <|> myStringLiteral '\'')
              regex = do
                s <- myStringLiteralNoBr '/'
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

--notFolBy a b = a <* notFollowedBy (char b)
folBy a b = a <* (lookAhead (char b) >>= const (return ()))
args' :: JMParser [JExpr]
args' = parens' $ commaSep expr

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
    exponent'       = do _ <- oneOf "eE"
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
    _ <- char t
    x <- concat <$> many myChar
    _ <- char t
    return x
 where myChar = do
         c <- noneOf [t]
         case c of
           '\\' -> do
                  c2 <- anyChar
                  return [c,c2]
           '\n' -> return "\\n"
           _ -> return [c]

myStringLiteralNoBr :: Char -> JMParser String
myStringLiteralNoBr t = do
    _ <- char t
    x <- concat <$> many myChar
    _ <- char t
    return x
 where myChar = do
         c <- noneOf [t,'\n']
         case c of
           '\\' -> do
                  c2 <- anyChar
                  return [c,c2]
           _ -> return [c]
