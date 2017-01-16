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
      exp = Parser.parse tokens
   in case Type.inferProgType exp of
        Nothing -> "Does not type check"
        Just ty -> let nf = Compiler.toNormalForm exp
                       nfCl = Compiler.toClosure nf
                       llvmIr = Compiler.Llvm.compile nfCl
                    in llvmIr

main :: IO ()
main = interact compileFile
