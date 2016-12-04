module Compiler.Llvm(compile) where

import qualified Data.List
import qualified Data.Tuple

import Compiler
import Control.Monad.Trans(lift)
import Data.List.NonEmpty(NonEmpty(..))
import FreshName

-- Eventually consider to switch to libgc

type Id = String
type Label = Id
type Register = Id

data Value = VId Id | VInt Integer

data Instr =
  Add   Id Value Value |
  Sub   Id Value Value |
  Mul   Id Value Value |
  Div   Id Value Value |
  CmpLT Id Value Value |
  CmpEQ Id Value Value |
  Cast  Id Value |
  Phi   Id [(Label, Value)] |
  Br    Label |
  Cbr   Value Label Label |
  Lbl   Label

type Subst = Id -> Value

instance Show Value where
  show (VId x) = x
  show (VInt n) = show n

instance Show Instr where
  show (Add x e1 e2) = "  " ++ x ++ " = add i64 " ++ show e1 ++ ", " ++ show e2
  show (Sub x e1 e2) = "  " ++ x ++ " = sub i64 " ++ show e1 ++ ", " ++ show e2
  show (Mul x e1 e2) = "  " ++ x ++ " = mul i64 " ++ show e1 ++ ", " ++ show e2
  show (Div x e1 e2) = "  " ++ x ++ " = udiv i64 " ++ show e1 ++ ", " ++ show e2
  show (CmpLT x e1 e2) = "  " ++ x ++ " = icmp ult i64 " ++ show e1 ++ ", " ++ show e2
  show (CmpEQ x e1 e2) = "  " ++ x ++ " = icmp eq i64 " ++ show e1 ++ ", " ++ show e2
  show (Cast x e) = "  " ++ x ++ " = zext i1 " ++ show e ++ " to i64"
  show (Phi x ys) = "  " ++ x ++ " = phi i64 " ++
    concat (Data.List.intersperse ", "
      (map (\(y, z) -> "[" ++ show z ++ ", %" ++ y ++ "]") ys))
  show (Br lbl) = "  br label %" ++ lbl
  show (Cbr x thenLabel elseLabel) =
    "  br i1 " ++ show x ++ ", label %" ++ thenLabel ++ ", label %" ++ elseLabel
  show (Lbl x) = x ++ ":"

freshVarName :: NameGen Id
freshVarName = do
  a <- fresh
  return ("%" ++ a)

freshLabelName :: NameGen Label
freshLabelName = fresh

compileAt :: AtomicExprCl -> Subst -> Value
compileAt (ACLitInt n) s = VInt n
compileAt (ACLitBool True) s = VInt 1
compileAt (ACLitBool False) s = VInt 0
compileAt (ACVar x) s = s x
compileAt _ _ = undefined

compileOp c e1 e2 s k = do
  alpha <- freshVarName
  let stmt = c alpha (compileAt e1 s) (compileAt e2 s)
  stmts <- k (VId alpha)
  return (stmt : stmts)

addCast k x = do
  alpha <- freshVarName
  let stmt = Cast alpha x
  stmts <- k (VId alpha)
  return (stmt : stmts)

compileCo :: ComplexExprCl -> Subst
        -> (Value -> NameGen [Instr])
        -> NameGen [Instr]
compileCo (CCOpAdd e1 e2) s k = compileOp Add   e1 e2 s k
compileCo (CCOpSub e1 e2) s k = compileOp Sub   e1 e2 s k
compileCo (CCOpMul e1 e2) s k = compileOp Mul   e1 e2 s k
compileCo (CCOpDiv e1 e2) s k = compileOp Div   e1 e2 s k
compileCo (CCOpLT e1 e2)  s k = compileOp CmpLT e1 e2 s (addCast k)
compileCo (CCOpEQ e1 e2)  s k = compileOp CmpEQ e1 e2 s (addCast k)
compileCo (CCIf b e1 e2)  s k = do
  alpha <- freshVarName
  label <- freshLabelName
  let thenLabel = label ++ "_then"
  let elseLabel = label ++ "_else"
  beta <- freshVarName
  gamma <- freshVarName
  let stmt0 = CmpEQ alpha (VInt 1) (compileAt b s)
  let stmt1 = Cbr (VId alpha) thenLabel elseLabel
  let stmt2 = Lbl thenLabel
  let stmt3 = Br label
  let stmt4 = Lbl elseLabel
  let stmt5 = Br label
  let stmt6 = Lbl label
  (
    fmap (\xs -> stmt0 : stmt1 : stmt2 : xs) (compileExpr e1 s (\e1' ->
    fmap (\xs -> stmt3 : stmt4 : xs) (compileExpr e2 s (\e2' ->
    fmap (\xs -> stmt5 : stmt6 : Phi gamma [(thenLabel, e1'), (elseLabel, e2')] : xs) (k (VId gamma)))))))
compileCo _ _ _ = undefined

compileExpr :: ExprNFCl -> Subst -> (Value -> NameGen [Instr]) -> NameGen [Instr]
compileExpr (ECVal x) s k  = k (compileAt x s)
compileExpr (ECLet x e1 e2) s k =
  compileCo e1 s (\e1' ->
  compileExpr e2 (\y -> if y == x then e1' else s y) k)

compile :: ExprNFCl -> String
compile e =
  let k = \result -> return [Add "%result" (VInt 0) result] in
  let instrs = runNameGen (compileExpr e VId k) in
  let toString [] = ""
      toString (x : xs) = show x ++ "\n" ++ toString xs in
  unlines [
      "declare i32 @printf(i8*, ...)",
      "@.str = private unnamed_addr constant [4 x i8] c\"%d\\0A\\00\"",
      "define i32 @main() {",
      toString instrs,
      "call i32 (i8*, ...)* @printf(",
        "i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), ",
        "i64 %result)",
      "ret i32 0",
      "}"
    ]
