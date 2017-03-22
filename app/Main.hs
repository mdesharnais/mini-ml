module Main where

import qualified Compiler
import qualified Compiler.Llvm
import qualified Lexer
import qualified Parser
import qualified System.Environment
import qualified TypeContext as TyContext
import qualified TypeInference as TyInference

compileFile :: String -> String
compileFile code =
  let tokens = Lexer.alexScanTokens code in
  let exp = Parser.parse tokens in
  case TyInference.infer2 TyContext.empty exp of
    Left msg -> msg
    Right expr ->
      let nf = Compiler.toNormalForm expr in
      let nfCl = Compiler.toClosure nf in
      let llvmIr = Compiler.Llvm.compile nfCl in
      --show expr ++ "\n\n\n\n\n" ++
      --show nf ++ "\n\n\n\n\n" ++
      --show nfCl ++ "\n\n\n\n\n" ++
      llvmIr

main :: IO ()
main = interact compileFile
