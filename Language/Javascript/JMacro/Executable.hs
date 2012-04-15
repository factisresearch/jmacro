module Main where

import Text.PrettyPrint.Leijen.Text (hPutDoc)
import Control.Applicative
import Control.Monad
import Language.Javascript.JMacro
import System.Environment
import System.Console.ParseArgs
import System.IO

main = do
   args <- parseArgsIO ArgsComplete
           [Arg "Scope" (Just 's') (Just "scope") Nothing "Enforce block scoping through global variable renames.",
            Arg "Help" (Just 'h') (Just "help") Nothing "",
            Arg "Infile"  Nothing Nothing (argDataOptional "Input file"  ArgtypeString) "Input file",
            Arg "Outfile" Nothing Nothing (argDataOptional "Output file" ArgtypeString) "Output file"]
   when (gotArg args "Help") $ usageError args "Transforms jmacro code into valid javascript."
   let s = gotArg args "Scope"
   infile <- getArgStdio args "Infile" ReadMode
   outfile <- getArgStdio args "Outfile" WriteMode
   either (hPrint stderr) (hPutDoc outfile) . parseIt s =<< hGetContents infile
  where
    parseIt True  = onRight (renderJs . scopify)  . parseJM
    parseIt False = onRight (renderJs . fixIdent) . parseJM
    onRight :: (a -> b) -> Either c a -> Either c b
    onRight f (Right x) = Right (f x)
    onRight _ (Left x) = (Left x)

    fixIdent x = fromMC $ composOp go (toMC x) :: JStat
        where go v = case v of
                       (MStat (DeclStat (StrI ('!':'!':i')) t)) -> MStat (DeclStat (StrI i') t)
                       (MStat (DeclStat (StrI ('!':i')) t)) -> MStat (DeclStat (StrI i') t)
                       _ -> composOp go v
