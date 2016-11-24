module Compiler.Llvm(compile) where

import qualified Parser
import qualified Lexer

import Compiler
import FreshName

compile e = unlines [
    "declare i32 @printf(i8*, ...)",
    "@.str = private unnamed_addr constant [4 x i8] c\"%d\\0A\\00\"",
    "define i32 @main() {",
    compileExpr e,
    "ret i32 0",
    "}"
  ]

type Id = String

data Value = VId Id | VInt Integer

data Instr =
  Add Value Value |
  Sub Value Value |
  Mul Value Value |
  Udiv Value Value

data Terminator =
  Br Id
--  Ret Value
--  Switch ...

type Stmt = (Id, Instr)
type Block = (Id, [Stmt], Terminator)
type Function = (Id, [Block])

-- comp_ :: Exp -> State FreshName LLVMVal
compileAt :: AtomicExprClosure -> String
compileAt (ACLitInt n) = show n
compileAt (ACLitBool True) = "1"
compileAt (ACLitBool False) = "0"
compileAt (ACVar x) = "%" ++ x
compileAt _ = undefined

compAt = compileAt

-- -> [Stmt]
compileCo :: ComplexExprClosure -> String
compileCo (COpAdd e1 e2) =  "add i32 "     ++ compAt e1 ++ ", " ++ compAt e2
compileCo (COpSub e1 e2) =  "sub i32 "     ++ compAt e1 ++ ", " ++ compAt e2
compileCo (COpMul e1 e2) =  "mul i32 "     ++ compAt e1 ++ ", " ++ compAt e2
compileCo (COpDiv e1 e2) = "udiv i32 "     ++ compAt e1 ++ ", " ++ compAt e2
--compileCo (COpLT  e1 e2) = "icmp ule i32 " ++ compAt e1 ++ ", " ++ compAt e2
--compileCo (COpEQ  e1 e2) = "icmp eq  i32 " ++ compAt e1 ++ ", " ++ compAt e2
compileCo _ = undefined

genPrintIntVar :: String -> String
genPrintIntVar x =
  "call i32 (i8*, ...)* @printf(" ++
    "i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), " ++
    "i32 " ++ x ++
  ")"

-- -> ([Block], [Function])
compileExpr :: ExprNFClosure -> String
compileExpr (EVal x)  = genPrintIntVar (compileAt x)
compileExpr (ELet x e1 e2) =
  "%" ++ x ++ " = " ++ compileCo e1 ++ "\n" ++ compileExpr e2
compileExpr _ = undefined


-- -> Function
-- compile
