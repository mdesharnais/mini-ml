module Main where

import qualified Compiler
import qualified Compiler.Llvm
import qualified Lexer
import qualified Parser
import qualified System.Environment
import qualified Type

compileFile :: String -> String
compileFile code =
  let tokens = Lexer.alexScanTokens code
      prog = Parser.parse tokens
      nf = Compiler.toNormalForm prog
      nfCl = Compiler.toClosure nf
      llvmIr = Compiler.Llvm.compile nfCl
   in llvmIr

main :: IO ()
main = interact compileFile
