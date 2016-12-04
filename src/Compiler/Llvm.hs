module Compiler.Llvm(compile) where

import qualified Control.Monad.State as State
import qualified Data.List as List
import qualified Data.Tuple

import Compiler
import Control.Monad.State(State)
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

type CompilationM a = NameGenT (State [Instr]) a

type Subst = Id -> Value

instance Show Value where
  show (VId x) = x
  show (VInt n) = show n

instance Show Instr where
  show (Add x e1 e2) = "  " ++ x ++ " = add i64 " ++ show e1 ++ ", " ++ show e2
  show (Sub x e1 e2) = "  " ++ x ++ " = sub i64 " ++ show e1 ++ ", " ++ show e2
  show (Mul x e1 e2) = "  " ++ x ++ " = mul i64 " ++ show e1 ++ ", " ++ show e2
  show (Div x e1 e2) = "  " ++ x ++ " = udiv i64 " ++ show e1 ++ ", " ++ show e2
  show (CmpLT x e1 e2) =
    "  " ++ x ++ " = icmp ult i64 " ++ show e1 ++ ", " ++ show e2
  show (CmpEQ x e1 e2) =
    "  " ++ x ++ " = icmp eq i64 " ++ show e1 ++ ", " ++ show e2
  show (Cast x e) = "  " ++ x ++ " = zext i1 " ++ show e ++ " to i64"
  show (Phi x ys) = "  " ++ x ++ " = phi i64 " ++
    concat (List.intersperse ", "
      (map (\(y, z) -> "[" ++ show z ++ ", %" ++ y ++ "]") ys))
  show (Br lbl) = "  br label %" ++ lbl
  show (Cbr x thenLabel elseLabel) =
    "  br i1 " ++ show x ++ ", label %" ++ thenLabel ++ ", label %" ++ elseLabel
  show (Lbl x) = x ++ ":"

runCompilation :: CompilationM a -> (a, [Instr])
runCompilation = flip State.runState [] . runNameGenT

addInstrs :: [Instr] -> CompilationM ()
addInstrs stmts = lift (State.modify (flip (++) stmts))

getCurrentLabel :: CompilationM (Maybe Label)
getCurrentLabel = do
  let isLabel (Lbl _) = True
      isLabel _ = False
  lift (State.gets (fmap (\(Lbl x) -> x) . List.find isLabel . reverse))

freshVarName :: CompilationM Id
freshVarName = do
  a <- fresh
  return ("%" ++ a)

freshLabelName :: CompilationM Label
freshLabelName = fresh

compileAt :: AtomicExprCl -> Subst -> Value
compileAt (ACLitInt n) s = VInt n
compileAt (ACLitBool True) s = VInt 1
compileAt (ACLitBool False) s = VInt 0
compileAt (ACVar x) s = s x
compileAt _ _ = undefined

compileOp c e1 e2 s = do
  alpha <- freshVarName
  let stmt = c alpha (compileAt e1 s) (compileAt e2 s)
  addInstrs [stmt]
  return (VId alpha)

addCast x = do
  alpha <- freshVarName
  let stmt = Cast alpha x
  addInstrs [stmt]
  return (VId alpha)

compileCo :: ComplexExprCl -> Subst -> CompilationM Value
compileCo (CCOpAdd e1 e2) s = compileOp Add   e1 e2 s
compileCo (CCOpSub e1 e2) s = compileOp Sub   e1 e2 s
compileCo (CCOpMul e1 e2) s = compileOp Mul   e1 e2 s
compileCo (CCOpDiv e1 e2) s = compileOp Div   e1 e2 s
compileCo (CCOpLT e1 e2)  s = compileOp CmpLT e1 e2 s >>= addCast
compileCo (CCOpEQ e1 e2)  s = compileOp CmpEQ e1 e2 s >>= addCast
compileCo (CCIf b e1 e2)  s = do
  alpha <- freshVarName
  label <- freshLabelName
  let thenLabel = label ++ "_then"
  let elseLabel = label ++ "_else"
  beta <- freshVarName
  gamma <- freshVarName
  let stmt0 = CmpEQ alpha (VInt 1) (compileAt b s)
  let stmt1 = Cbr (VId alpha) thenLabel elseLabel
  let stmt2 = Lbl thenLabel
  addInstrs [stmt0, stmt1, stmt2]
  e1' <- compileExpr e1 s
  e1LabelOpt <- getCurrentLabel
  let e1Label = maybe thenLabel id e1LabelOpt
  let stmt3 = Br label
  let stmt4 = Lbl elseLabel
  addInstrs [stmt3, stmt4]
  e2' <- compileExpr e2 s
  e2LabelOpt <- getCurrentLabel
  let e2Label = maybe thenLabel id e2LabelOpt
  let stmt5 = Br label
  let stmt6 = Lbl label
  let stmt7 = Phi gamma [(e1Label, e1'), (e2Label, e2')]
  addInstrs [stmt5, stmt6, stmt7]
  return (VId gamma)
compileCo _ _ = undefined

compileExpr :: ExprNFCl -> Subst -> CompilationM Value
compileExpr (ECVal x) s = return (compileAt x s)
compileExpr (ECLet x e1 e2) s = do
  e1' <- compileCo e1 s
  e2' <- compileExpr e2 (\y -> if y == x then e1' else s y)
  return e2'

compile :: ExprNFCl -> String
compile e =
  let (result, instrs) = runCompilation (compileExpr e VId) in
  let toString [] = ""
      toString (x : xs) = show x ++ "\n" ++ toString xs in
  unlines [
      "declare i32 @printf(i8*, ...)",
      "@.str = private unnamed_addr constant [4 x i8] c\"%d\\0A\\00\"",
      "define i32 @main() {",
      toString instrs,
      "call i32 (i8*, ...)* @printf(",
        "i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), ",
        "i64 " ++ show result ++ ")",
      "ret i32 0",
      "}"
    ]
