module Main where

import qualified Lexer
import qualified Parser
import qualified System.Environment
import qualified Type

compileFile :: String -> IO ()
compileFile filename = do
  srcCode <- readFile filename
  let tokens = Lexer.alexScanTokens srcCode
  let prog = Parser.parse tokens
  print prog

main :: IO ()
main = do
  args <- System.Environment.getArgs
  mapM_ compileFile args
