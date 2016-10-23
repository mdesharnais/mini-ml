module Main where

import qualified Lexer
import qualified System.Environment

compileFile :: String -> IO ()
compileFile filename = do
  prog <- readFile filename
  let tokens = Lexer.alexScanTokens prog
  print tokens

main :: IO ()
main = do
  args <- System.Environment.getArgs
  mapM_ compileFile args
