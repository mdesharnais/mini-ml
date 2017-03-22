{-# LANGUAGE NamedFieldPuns #-}

module Compiler.Llvm(compile) where

import qualified Control.Monad.State as State
import qualified Control.Monad.Trans as MonadTrans
import qualified Data.Foldable as Foldable
import qualified Data.List as List
import qualified Data.Set as Set

import Compiler
import Control.Monad.State(StateT)
import Data.List.NonEmpty(NonEmpty(..))
import FreshName
import Text.Printf(printf)
import Type

import Debug.Trace(traceShowId)

-- Eventually consider to switch to libgc

type Id = String
type Label = Id

data Value = VId Id | VInt Integer | VUndef

type SrcType = String
type DstType = String
type ValType = String
type VarType = String

data Instr =
  Add   Id Value Value |
  Sub   Id Value Value |
  Mul   Id Value Value |
  Div   Id Value Value |
  CmpLT Id Value Value |
  CmpEQ Id Value Value |
  Call  Id VarType Value [(Value, ValType)] |
  Cast  Id Value |
  Phi   Id [(Label, Value)] |
  Br    Label |
  Cbr   Value Label Label |
  Ret   Value ValType |
  Lbl   Label |
  Malloc Id Integer |
  Bitcast Id Value SrcType DstType |
  Load Id (SrcType, Value) |
  Store (SrcType, Value) (DstType, Value) |
  Ptrtoint Id Value SrcType DstType |
  Inttoptr Id Value SrcType DstType |
  Insertvalue Id (Value, SrcType) (Value, ValType) (NonEmpty Integer) |
  Extractvalue Id Value SrcType Integer

data Function = Function {
  funName :: Id,
  funArg :: Id,
  funType :: Type2,
  funInstrs :: [Instr]
}

data CompState = CompState {
  csExternVars :: [Id],
  csFuns :: [Function],
  csInstrs :: [Instr],
  csEnvSize :: Integer
}

emptyCompState = CompState {
  csExternVars = [],
  csFuns = [],
  csInstrs = [],
  csEnvSize = 0
}

type CompilationM a = StateT CompState NameGen a

runCompilation :: CompilationM a -> CompState -> (a, CompState)
runCompilation m s = runNameGen (State.runStateT m s)

llvmFunPtrType = "i64 (i64, i64)*"
llvmArrayType n = "[" ++ show n ++ " x i64]"
llvmClosureType n = "{" ++ llvmFunPtrType ++ ", " ++ llvmArrayType n ++ "}"

typeToLlvm :: Type2 -> String
typeToLlvm TBool = "i1"
typeToLlvm TInt = "i64"
typeToLlvm (TFun b t1 t2) =
  if Set.member AClo b then
    "i64"
  else
    typeToLlvm t2 ++ "(" ++ typeToLlvm t1 ++ ")*"
typeToLlvm (TVar _) = undefined

instance Show Function where
  show (Function { funName, funArg, funType, funInstrs }) =
    case funType of
      (TFun b t1 t2) ->
        if Set.member AClo b then
          "define " ++ typeToLlvm t2 ++ " " ++ funName ++
          "(i64 %closure, " ++ typeToLlvm t1 ++ " " ++ funArg ++ ") {\n" ++
            unlines (map show funInstrs) ++
          "}"
        else
          "define " ++ typeToLlvm t2 ++ " " ++ funName ++ "(" ++
            typeToLlvm t1 ++ " " ++ funArg ++
          ") {\n" ++
            unlines (map show funInstrs) ++
          "}"
      _ -> undefined

instance Show Value where
  show (VId x) = x
  show (VInt n) = show n
  show (VUndef) = "undef"

instance Show Instr where
  show (Add x e1 e2) = printf "  %s = add i64 %s, %s" x (show e1) (show e2)
  show (Sub x e1 e2) = printf "  %s = sub i64 %s, %s" x (show e1) (show e2)
  show (Mul x e1 e2) = printf "  %s = mul i64 %s, %s" x (show e1) (show e2)
  show (Div x e1 e2) = printf "  %s = sdiv i64 %s, %s" x (show e1) (show e2)
  show (CmpLT x e1 e2) =
    printf "  %s = icmp slt i64 %s, %s" x (show e1) (show e2)
  show (CmpEQ x e1 e2) =
    printf "  %s = icmp eq i64 %s, %s" x (show e1) (show e2)
  show (Call x ty f args) =
    printf "  %s = call %s %s(%s)" x ty (show f)
      (List.intercalate ", " (map (\(x, xTy) -> xTy ++ " " ++ show x) args))
  show (Cast x e) = printf "  %s = zext i1 %s to i64" x (show e)
  show (Phi x ys) = "  " ++ x ++ " = phi i64 " ++ concat (List.intersperse ", "
      (map (\(y, z) -> "[" ++ show z ++ ", %" ++ y ++ "]") ys))
  show (Br lbl) = "  br label %" ++ lbl
  show (Cbr x thenLabel elseLabel) =
    printf "  br i1 %s, label %%%s, label %%%s" (show x) thenLabel elseLabel
  show (Ret e ty) = "  ret " ++ ty ++ " " ++ show e
  show (Lbl x) = x ++ ":"
  show (Malloc x n) =
    --printf "  %s = call i8* @GC_malloc(i64 %d)" x n
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
  show (Insertvalue x (e1, srcTy) (e2, ty) is) =
    printf "  %s = insertvalue %s %s, %s %s, %s" x srcTy (show e1) ty (show e2)
      (Foldable.foldl1 (\a b -> a ++ ", " ++ b) (fmap show is))
  show (Extractvalue x e srcTy n) =
    printf "  %s = extractvalue %s %s, %d" x srcTy (show e) n

addFunctions :: [Function] -> CompilationM ()
addFunctions funs = State.modify (\cs -> cs { csFuns = csFuns cs ++ funs })

addInstrs :: [Instr] -> CompilationM ()
addInstrs stmts = State.modify (\cs -> cs { csInstrs = csInstrs cs ++ stmts })

addExternals :: [Id] -> CompilationM ()
addExternals fs = State.modify (\cs -> cs { csExternVars = List.union fs (csExternVars cs) })

promoteToFunction :: Id -> Type2 -> Id -> Integer -> Value -> CompilationM ()
promoteToFunction f fTy@(TFun b _ t2) x envLength result = do
  let stmtRet = Ret result (typeToLlvm t2)
  getInstrs <-
    if Set.member AClo b then do
      alpha <- freshVarName
      beta <- freshVarName
      let n = envLength
      let clTy = llvmClosureType n
      let clPtrTy = clTy ++ "*"
      let stmt0 = Inttoptr alpha (VId "%closure") "i64" clPtrTy
      let stmt1 = Load beta (clPtrTy, VId alpha)
      let stmt2 = Extractvalue "%self" (VId beta) clTy 0
      let stmt3 = Extractvalue "%env"  (VId beta) clTy 1
      return (\stmts -> [stmt0, stmt1, stmt2, stmt3] ++ stmts ++ [stmtRet])
    else
      return (\stmts -> stmts ++ [stmtRet])
  State.modify $ \cs ->
    let newFun = Function {
      funName = f,
      funArg = x,
      funType = fTy,
      funInstrs = getInstrs (csInstrs cs)
    } in
    cs {
      csFuns = newFun : csFuns cs,
      csInstrs = [],
      csEnvSize = 0
    }

getCurrentLabel :: CompilationM (Maybe Label)
getCurrentLabel =
  let isLabel (Lbl _) = True
      isLabel _ = False
   in State.gets
        (fmap (\(Lbl x) -> x) . List.find isLabel . reverse . csInstrs)

freshVarName :: CompilationM Id
freshVarName = do
  alpha <- MonadTrans.lift fresh
  return ("%" ++ alpha)

freshLabelName :: CompilationM Label
freshLabelName = MonadTrans.lift fresh

freshFunctionName :: CompilationM Id
freshFunctionName = do
  alpha <- MonadTrans.lift fresh
  return ("@" ++ alpha)

compileAt :: AtomicExprCl -> (Id -> Value) -> CompilationM Value
compileAt (ACLitInt  _ n) s = return (VInt n)
compileAt (ACLitBool _ True) s = return (VInt 1)
compileAt (ACLitBool _ False) s = return (VInt 0)
compileAt (ACExternVar _ x) s = do
  addExternals [x]
  return (VId ("@" ++ x))
compileAt (ACVar _ x) s = return (s x)
compileAt (ACVarSelf (TFun b _ _) f) s =
  if Set.member AClo b then
    return (VId "%closure")
  else
    return (VId ("@" ++ f))
compileAt (ACVarEnv ty n) s = do
  alpha <- freshVarName
  envSize <- State.gets csEnvSize
  addInstrs [Extractvalue alpha (VId "%env") (llvmArrayType envSize) n]
  case ty of
    TBool -> do
      beta <- freshVarName
      addInstrs [CmpEQ beta (VInt 1) (VId alpha)]
      return (VId beta)
    TInt -> return (VId alpha)
    fTy@(TFun b t1 t2) ->
      if Set.member AClo b then
        return (VId alpha)
      else do
        beta <- freshVarName
        addInstrs [Inttoptr beta (VId alpha) "i64" (typeToLlvm fTy)]
        return (VId beta)
    (TVar _) -> undefined

compileOp c e1 e2 s = do
  e1' <- compileAt e1 s
  e2' <- compileAt e2 s
  alpha <- freshVarName
  let stmt = c alpha e1' e2'
  addInstrs [stmt]
  return (VId alpha)

addCastBoolToInt64 x = do
  alpha <- freshVarName
  let stmt = Cast alpha x
  addInstrs [stmt]
  return (VId alpha)

compileCo :: ComplexExprCl -> (Id -> Value) -> CompilationM Value
compileCo (CCOpAdd _ e1 e2) s = compileOp Add   e1 e2 s
compileCo (CCOpSub _ e1 e2) s = compileOp Sub   e1 e2 s
compileCo (CCOpMul _ e1 e2) s = compileOp Mul   e1 e2 s
compileCo (CCOpDiv _ e1 e2) s = compileOp Div   e1 e2 s
compileCo (CCOpLT  _ e1 e2) s = compileOp CmpLT e1 e2 s
compileCo (CCOpEQ  _ e1 e2) s = compileOp CmpEQ e1 e2 s
compileCo (CCIf    _ b e1 e2) s = do
  b' <- compileAt b s
  --alpha <- freshVarName
  --let stmt0 = CmpEQ alpha (VInt 1) b'
  label <- freshLabelName
  let thenLabel = label ++ "_then"
  let elseLabel = label ++ "_else"
  let stmt1 = Cbr b' thenLabel elseLabel
  let stmt2 = Lbl thenLabel
  addInstrs [{-stmt0,-} stmt1, stmt2]
  e1' <- compileExpr e1 s
  e1LabelOpt <- getCurrentLabel
  let e1Label = maybe thenLabel id e1LabelOpt
  let stmt3 = Br label
  let stmt4 = Lbl elseLabel
  addInstrs [stmt3, stmt4]
  e2' <- compileExpr e2 s
  beta <- freshVarName
  e2LabelOpt <- getCurrentLabel
  let e2Label = maybe thenLabel id e2LabelOpt
  let stmt5 = Br label
  let stmt6 = Lbl label
  let stmt7 = Phi beta [(e1Label, e1'), (e2Label, e2')]
  addInstrs [stmt5, stmt6, stmt7]
  return (VId beta)
compileCo (CCClosure fTy@(TFun b _ _) x e env) s = do
  let isClosure = Set.member AClo b
  let envSize = toInteger (length env)
  alpha <- freshFunctionName
  (e', cs) <- MonadTrans.lift (State.runStateT (do
      beta <- freshVarName
      e' <- compileExpr e (\y -> if y == x then VId beta else s y)
      promoteToFunction alpha fTy beta envSize e')
        (emptyCompState { csEnvSize = envSize }))
  addFunctions (csFuns cs)
  addExternals (csExternVars cs)
  (epsilon, instrs) <-
    if isClosure then do
      let closureTy = llvmClosureType envSize
      let closurePtrTy = closureTy ++ "*"
      aaa <- freshVarName
      let stmt0 = Insertvalue aaa
            (VUndef, closureTy) (VId alpha, llvmFunPtrType) (0 :| [])
      (_, ccc, stmts) <- Foldable.foldlM (\(n, id, stmts) var -> do
        var' <- compileAt var s
        (var'', instrs) <-
          case atExprGetType var of
            TBool -> do
              alpha <- freshVarName
              return (VId alpha, [Cast alpha var'])
            TInt -> return (var', [])
            fTy@(TFun b _ _) ->
              if Set.member AClo b then
                return (var', [])
              else do
                alpha <- freshVarName
                return (VId alpha, [Ptrtoint alpha var' (typeToLlvm fTy) "i64"])
            (TVar _) -> undefined
        bbb <- freshVarName
        let stmt = Insertvalue bbb (id, closureTy) (var'', "i64") (1 :| [n])
        return (n + 1, VId bbb, instrs ++ (stmt : stmts))) (0, VId aaa, []) env
      gamma <- freshVarName
      delta <- freshVarName
      epsilon <- freshVarName
      let stmt1 = Malloc gamma (8 + 8 * envSize)
      let stmt2 = Bitcast delta (VId gamma) "i8*" closurePtrTy
      let stmt3 = Store (closureTy, ccc) (closurePtrTy, VId delta)
      let stmt4 = Ptrtoint epsilon (VId delta) closurePtrTy "i64"
      return (epsilon, stmt0 : reverse stmts ++ [stmt1, stmt2, stmt3, stmt4])
    else
      return (alpha, [])
  addInstrs instrs
  return (VId epsilon)
compileCo (CCApp _ (ACExternVar (TFun _ _ t2) f) e) s = do
  alpha <- freshVarName
  e' <- compileAt e s
  let eTy = typeToLlvm (atExprGetType e)
  let stmt = Call alpha (typeToLlvm t2) (VId ("@" ++ f)) [(e', eTy)]
  addExternals [f]
  addInstrs [stmt]
  return (VId alpha)
compileCo (CCApp _ (ACVarSelf (TFun b _ t2) f) e2) s = do
  let e2Ty = typeToLlvm (atExprGetType e2)
  alpha <- freshVarName
  e2' <- compileAt e2 s
  if Set.member AClo b then
    addInstrs [Call alpha (typeToLlvm t2) (VId "%self") [
      (VId "%closure", "i64"),
      (e2', e2Ty)]]
  else
    addInstrs [Call alpha (typeToLlvm t2) (VId ("@" ++ f)) [(e2', e2Ty)]]
  return (VId alpha)
compileCo (CCApp _ e1 e2) s = do
  let e1Ty = typeToLlvm (atExprGetType e1)
  let e2Ty = typeToLlvm (atExprGetType e2)
  e1' <- compileAt e1 s
  e2' <- compileAt e2 s
  case atExprGetType e1 of
    (TFun b _ t2) ->
      if Set.member AClo b then do
        alpha <- freshVarName
        beta <- freshVarName
        gamma <- freshVarName
        delta <- freshVarName
        let clTy = llvmClosureType 0
        let clPtrTy = clTy ++ "*"
        let stmt0 = Inttoptr alpha e1' "i64" clPtrTy
        let stmt1 = Load beta (clPtrTy, VId alpha)
        let stmt2 = Extractvalue gamma (VId beta) clTy 0
        let stmt3 =
              Call delta (typeToLlvm t2) (VId gamma) [(e1', e1Ty), (e2', e2Ty)]
        addInstrs [stmt0, stmt1, stmt2, stmt3]
        return (VId delta)
      else do
        delta <- freshVarName
        addInstrs [Call delta (typeToLlvm t2) e1' [(e2', e2Ty)]]
        return (VId delta)
    _ -> undefined

compileExpr :: ExprNFCl -> (Id -> Value) -> CompilationM Value
compileExpr (ECVal _ x) s = compileAt x s
compileExpr (ECLet _ x e1 e2) s = do
  e1' <- compileCo e1 s
  e2' <- compileExpr e2 (\y -> if y == x then e1' else s y)
  return e2'

compile :: ExprNFCl -> String
compile e =
  let showExtern f = "declare i64 @" ++ f ++ "(i64)" in
  let (result, cs) = runCompilation (compileExpr e VId) emptyCompState in
  unlines [
      "; Implementation defined external declarations",
      --"declare i8* @GC_malloc(i64)",
      "declare i8* @malloc(i64)",
      "; User defined external declarations",
      unlines (map showExtern (csExternVars cs)),
      "; User defined functions",
      unlines (map show (csFuns cs)),
      "define i32 @main() {",
      unlines (map show (csInstrs cs)),
      "  ret i32 0",
      "}"
    ]
