module Compiler.Llvm(compile) where

import qualified Control.Monad.State as State
import qualified Data.List as List
import qualified Data.Tuple

import Compiler
import Control.Monad.State(State)
import Control.Monad.Trans(lift)
import Data.List.NonEmpty(NonEmpty(..))
import FreshName
import Text.Printf(printf)

-- Eventually consider to switch to libgc

type Id = String
type Label = Id
type Register = Id

data Value = VId Id | VInt Integer | VConst String

type SrcType = String
type DstType = String

data Instr =
  Add   Id Value Value |
  Sub   Id Value Value |
  Mul   Id Value Value |
  Div   Id Value Value |
  CmpLT Id Value Value |
  CmpEQ Id Value Value |
  Call  Id Value Value Value |
  Cast  Id Value |
  Phi   Id [(Label, Value)] |
  Br    Label |
  Cbr   Value Label Label |
  Ret   Value |
  Lbl   Label |
  Malloc Id Integer |
  Bitcast Id Value SrcType DstType |
  Load Id (SrcType, Value) |
  Store (SrcType, Value) (DstType, Value) |
  Ptrtoint Id Value SrcType DstType |
  Inttoptr Id Value SrcType DstType |
  Extractvalue Id Value SrcType Integer

-- (function name, arg name, instructions)
type Function = (Id, Id, [Instr])
type CompilationState = ([Function], [Instr])
type CompilationM a = NameGenT (State CompilationState) a

type Subst = Id -> Value

llvmFunPtrType = "i64 (i64, i64)*"
llvmArrayType n = "[" ++ show n ++ " x i64]"
llvmClosureType n = "{" ++ llvmFunPtrType ++ ", " ++ llvmArrayType n ++ "}"
llvmArrayLiteral [] = "[ ]"
llvmArrayLiteral (x : xs) =
  "[" ++ foldl ((++) . (", " ++)) (show x) (map show xs) ++ "]"

instance Show Value where
  show (VId x) = x
  show (VInt n) = show n
  show (VConst str) = str

instance Show Instr where
  show (Add x e1 e2) = printf "  %s = add i64 %s, %s" x (show e1) (show e2)
  show (Sub x e1 e2) = printf "  %s = sub i64 %s, %s" x (show e1) (show e2)
  show (Mul x e1 e2) = printf "  %s = mul i64 %s, %s" x (show e1) (show e2)
  show (Div x e1 e2) = printf "  %s = udiv i64 %s, %s" x (show e1) (show e2)
  show (CmpLT x e1 e2) =
    printf "  %s = icmp ult i64 %s, %s" x (show e1) (show e2)
  show (CmpEQ x e1 e2) =
    printf "  %s = icmp eq i64 %s, %s" x (show e1) (show e2)
  show (Call x f cl n) =
    printf "  %s = call i64 %s(i64 %s, i64 %s)" x (show f) (show cl) (show n)
  show (Cast x e) = printf "  %s = zext i1 %s to i64" x (show e)
  show (Phi x ys) = "  " ++ x ++ " = phi i64 " ++
    concat (List.intersperse ", "
      (map (\(y, z) -> "[" ++ show z ++ ", %" ++ y ++ "]") ys))
  show (Br lbl) = "  br label %" ++ lbl
  show (Cbr x thenLabel elseLabel) =
    printf "  br i1 %s, label %%%s, label %%%s" (show x) thenLabel elseLabel
  show (Ret e) = "  ret i64 " ++ show e
  show (Lbl x) = x ++ ":"
  show (Malloc x n) =
    printf "  %s = call i8* @malloc(i64 %d)" x n
  show (Bitcast x e srcTy dstTy) =
    printf "  %s = bitcast %s %s to %s" x srcTy (show e) dstTy
  show (Load x (ty, e)) =
    printf "  %s = load %s %s" x ty (show e)
  show (Store (ty1, e1) (ty2, e2)) =
    printf "  store %s %s, %s %s" ty1 (show e1) ty2 (show e2)
  show (Ptrtoint x e srcTy dstTy) =
    printf "  %s = ptrtoint %s %s to %s" x srcTy (show e) dstTy
  show (Inttoptr x e srcTy dstTy) =
    printf "  %s = inttoptr %s %s to %s" x srcTy (show e) dstTy
  show (Extractvalue x e srcTy n) =
    printf "  %s = extractvalue %s %s, %d" x srcTy (show e) n

runCompilation :: CompilationM a -> CompilationState -> (a, CompilationState)
runCompilation m s = State.runState (runNameGenT m) s

addFunctions :: [Function] -> CompilationM ()
addFunctions funs =
  let mapPair f g (x, y) = (f x, g y) in
  lift (State.modify (mapPair (flip (++) funs) id))

addInstrs :: [Instr] -> CompilationM ()
addInstrs stmts =
  let mapPair f g (x, y) = (f x, g y) in
  lift (State.modify (mapPair id (flip (++) stmts)))

promoteToFunction :: Id -> Id -> Integer -> Value -> CompilationM ()
promoteToFunction f x envLength result = do
  alpha <- freshVarName
  beta <- freshVarName
  let n = envLength
  let clTy = llvmClosureType n
  let clPtrTy = clTy ++ "*"
  let stmt0 = Inttoptr alpha (VId "%closure") "i64" clPtrTy
  let stmt1 = Load beta (clPtrTy, VId alpha)
  let stmt2 = Extractvalue "%self" (VId beta) clTy 0
  let stmt3 = Extractvalue "%env"  (VId beta) clTy 1
  lift $ State.modify $ \(funs, stmts) ->
    ((f, x, [stmt0, stmt1, stmt2, stmt3] ++ stmts ++ [Ret result]) : funs, [])

getCurrentLabel :: CompilationM (Maybe Label)
getCurrentLabel = do
  let isLabel (Lbl _) = True
      isLabel _ = False
  lift (State.gets (fmap (\(Lbl x) -> x) . List.find isLabel . reverse . snd))

freshVarName :: CompilationM Id
freshVarName = fmap ("%" ++) fresh

freshLabelName :: CompilationM Label
freshLabelName = fresh

freshFunctionName :: CompilationM Id
freshFunctionName = fmap ("@" ++) fresh

compileAt :: AtomicExprCl -> Subst -> Value
compileAt (ACLitInt n) s = VInt n
compileAt (ACLitBool True) s = VInt 1
compileAt (ACLitBool False) s = VInt 0
compileAt (ACVar x) s = s x
compileAt (ACVarEnv n) s = undefined
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
compileCo (CCOpLT  e1 e2) s = compileOp CmpLT e1 e2 s >>= addCast
compileCo (CCOpEQ  e1 e2) s = compileOp CmpEQ e1 e2 s >>= addCast
compileCo (CCIf  b e1 e2) s = do
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
compileCo (CCClosure x e env) s = do
  let envLenght = toInteger (length env)
  alpha <- freshFunctionName
  let (e', (funs, [])) =
        runCompilation (do
          beta <- freshVarName
          e' <- compileExpr e (\y -> if y == x then VId beta else s y)
          promoteToFunction alpha beta envLenght e') ([], [])
  addFunctions funs
  gamma <- freshVarName
  delta <- freshVarName
  epsilon <- freshVarName
  let closureType = llvmClosureType envLenght
  let closurePtrType = closureType ++ "*"
  let stmt0 = Malloc gamma (8 + 8 * envLenght)
  let stmt1 = Bitcast delta (VId gamma) "i8*" closurePtrType
  let closure = VConst ("{" ++
          llvmFunPtrType ++ " " ++ alpha ++ ", " ++
          llvmArrayType envLenght ++ " " ++ llvmArrayLiteral env ++
        "}")
  let stmt2 = Store (closureType, closure) (closurePtrType, VId delta)
  let stmt3 = Ptrtoint epsilon (VId delta) closurePtrType "i64"
  addInstrs [stmt0, stmt1, stmt2, stmt3]
  return (VId epsilon)
compileCo (CCApp e1 e2) s = do
  alpha <- freshVarName
  beta <- freshVarName
  gamma <- freshVarName
  delta <- freshVarName
  let clTy = llvmClosureType 0
  let clPtrTy = clTy ++ "*"
  let e1' = compileAt e1 s
  let stmt0 = Inttoptr alpha e1' "i64" clPtrTy
  let stmt1 = Load beta (clPtrTy, VId alpha)
  let stmt2 = Extractvalue gamma (VId beta) clTy 0
  let stmt3 = Call delta (VId gamma) e1' (compileAt e2 s)
  addInstrs [stmt0, stmt1, stmt2, stmt3]
  return (VId delta)

compileExpr :: ExprNFCl -> Subst -> CompilationM Value
compileExpr (ECVal x) s = return (compileAt x s)
compileExpr (ECLet x e1 e2) s = do
  e1' <- compileCo e1 s
  e2' <- compileExpr e2 (\y -> if y == x then e1' else s y)
  return e2'

compile :: ExprNFCl -> String
compile e =
  let (result, (funs, instrs)) = runCompilation (compileExpr e VId) ([], []) in
  let showFun (f, x, b) =
        "define i64 " ++ f ++ "(i64 %closure, i64 " ++ x ++ ") {\n" ++
          unlines (map show b) ++
        "}" in
  unlines [
      "declare i32 @printf(i8*, ...)",
      "declare i8* @malloc(i64)",
      unlines (map showFun funs),
      "@.str = private unnamed_addr constant [4 x i8] c\"%d\\0A\\00\"",
      "define i32 @main() {",
      unlines (map show instrs),
      "  call i32 (i8*, ...)* @printf(",
      "    i8* getelementptr inbounds ([4 x i8]* @.str, i32 0, i32 0), ",
      "    i64 " ++ show result ++ ")",
      "  ret i32 0",
      "}"
    ]
