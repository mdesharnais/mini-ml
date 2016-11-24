module Compiler.Llvm where

import qualified Parser
import qualified Lexer

import Compiler
import FreshName

type Id = String
type Code = String

freshVarName :: NameGen Id
freshVarName = do
  a <- fresh
  return ("%" ++ a)

freshVarInt:: Integer -> NameGen (Id, Code)
freshVarInt n = do
  nPtr <- freshVarName
  nName <- freshVarName
  return (nName,
    nPtr ++ " = alloca i32\n" ++
    "store i32 " ++ show n ++ ", i32* " ++ nPtr ++ "\n" ++
    nName ++ " = load i32* " ++ nPtr ++ "\n")

testCompile prog = runNameGen $ do
  nf <- Compiler.toNormalFormM (Parser.parse (Lexer.alexScanTokens prog))
  llvmIr <- compile (Compiler.toClosure nf)
  return (unlines [
      "declare i32 @printf(i8*, ...)",
      "@.str = private unnamed_addr constant [4 x i8] c\"%d\\0A\\00\"",
      "define i32 @main() {",
      llvmIr,
      "%dummy = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), i32 %result)",
      "ret i32 0",
      "}"
    ])

compileAt :: AtomicExprClosure -> String
compileAt (ACLitInt n) = "i32 " ++ show n
compileAt (ACLitBool True) = "i1 1"
compileAt (ACLitBool False) = "i1 1"
compileAt (ACVar x) = "i32 %" ++ x
compileAt _ = undefined

compileCo :: ComplexExprClosure -> NameGen (Id, Code)
compileCo (COpAdd (ACLitInt n1) (ACLitInt n2)) = do
  (n1Id, n1Code) <- freshVarInt n1
  (n2Id, n2Code) <- freshVarInt n2
  result <- freshVarName
  return (result,
    n1Code ++ n2Code ++
    result ++ " = add i32 " ++ n1Id ++ ", " ++ n2Id ++ "\n")
compileCo _ = undefined

compile :: ExprNFClosure -> NameGen String
compile (EVal (ACLitInt n)) = do
  return (
    "%result_ptr = alloca i32\n" ++
    "store i32 " ++ show n ++ ", i32* %result_ptr\n" ++
    "%result = load i32* %result_ptr\n")
compile (EVal (ACLitBool b)) = do
  let n = if b then 1 else 0
  return (
    "%result_ptr = alloca i32\n" ++
    "store i32 " ++ show n ++ ", i32* %result_ptr\n" ++
    "%result = load i32* %result_ptr\n")
compile (EVal (ACVar x)) = do
  return (
    "%result_ptr = alloca i32\n" ++
    "store i32 %" ++ x ++ ", i32* %result_ptr\n" ++
    "%result = load i32* %result_ptr\n")
compile (EVal _) = undefined
compile (ELet x e1 e2) = do
  (e1Name, e1Code) <- compileCo e1
  a <- freshVarName
  e2' <- compile e2
  return (
    e1Code ++
    a ++ " = alloca i32\n" ++
    "store i32 " ++ e1Name ++ ", i32* " ++ a ++ "\n" ++
    "%" ++ x ++ " = load i32* " ++ a ++ "\n" ++
    e2')
compile _ = undefined
