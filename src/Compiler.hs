{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module Compiler where

import qualified Data.List

import Data.List((\\))
import Expr(TyExpr(..), Id)
import FreshName
import Type(Type)

-- Intermediate language in normal form

type Expr = TyExpr Type

data AtomicExpr =
  ALitInt Integer |
  ALitBool Bool |
  AVar Id |
  AExternVar Id

data ComplexExpr =
  COpAdd AtomicExpr AtomicExpr |
  COpSub AtomicExpr AtomicExpr |
  COpMul AtomicExpr AtomicExpr |
  COpDiv AtomicExpr AtomicExpr |
  COpLT AtomicExpr AtomicExpr |
  COpEQ AtomicExpr AtomicExpr |
  CIf AtomicExpr ExprNF ExprNF |
  CApp AtomicExpr AtomicExpr |
  CAbs (Id, Type) ExprNF

data ExprNF =
  EVal AtomicExpr |
  ELet Id ComplexExpr ExprNF |
  ELetRec Id ((Id, Type), ExprNF) ExprNF

-- Pretty print

instance Show AtomicExpr where
  show (ALitInt n) = show n
  show (ALitBool n) = show n
  show (AVar x) = x
  show (AExternVar x) = x

instance Show ComplexExpr where
  show (COpAdd e1 e2) = show e1 ++ " + " ++ show e2
  show (COpSub e1 e2) = show e1 ++ " - " ++ show e2
  show (COpMul e1 e2) = show e1 ++ " * " ++ show e2
  show (COpDiv e1 e2) = show e1 ++ " / " ++ show e2
  show (COpLT e1 e2) = show e1 ++ " < " ++ show e2
  show (COpEQ e1 e2) = show e1 ++ " = " ++ show e2
  show (CIf e1 e2 e3) =
    "if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3
  show (CApp e1 e2) = show e1 ++ " " ++ show e2
  show (CAbs (x, ty) e) =
    "(fun " ++ x ++ " : " ++ show ty ++ " -> " ++ show e ++ ")"

instance Show ExprNF where
  show (EVal x) = show x
  show (ELet x e1 e2) =
    "let " ++ x ++ " = " ++ show e1 ++ " in\n" ++ show e2
  show (ELetRec f ((x, ty), e1) e2) =
    "let rec " ++ f ++ " = (fun " ++ x ++ " : " ++ show ty ++ " -> " ++
      show e1 ++ ") in\n" ++ show e2

-- Expression -> normal form

nfBinOp :: Expr -> Expr -> (AtomicExpr -> AtomicExpr -> ComplexExpr) ->
  (Id -> AtomicExpr) -> (AtomicExpr -> NameGen ExprNF) -> NameGen ExprNF
nfBinOp e1 e2 op s k = nf e1 s (\a -> nf e2 s (\b -> do
  c <- fresh
  d <- k (AVar c)
  return (ELet c (op a b) d)))

nf :: Expr ->
  (Id -> AtomicExpr) ->
  (AtomicExpr -> NameGen ExprNF) ->
  NameGen ExprNF
nf (LitInt n) s k = k (ALitInt n)
nf (LitBool b) s k = k (ALitBool b)
nf (Var x) s k = k (s x)
nf (ExternVar x) s k = k (AExternVar x)
nf (OpAdd e1 e2) s k = nfBinOp e1 e2 COpAdd s k
nf (OpSub e1 e2) s k = nfBinOp e1 e2 COpSub s k
nf (OpMul e1 e2) s k = nfBinOp e1 e2 COpMul s k
nf (OpDiv e1 e2) s k = nfBinOp e1 e2 COpDiv s k
nf (OpLT e1 e2) s k = nfBinOp e1 e2 COpLT s k
nf (OpEQ e1 e2) s k = nfBinOp e1 e2 COpEQ s k
nf (If e1 e2 e3) s k = nf e1 s (\e1' -> do
  a <- fresh
  e2' <- nf e2 s (return . EVal)
  e3' <- nf e3 s (return . EVal)
  b <- k (AVar a)
  return (ELet a (CIf e1' e2' e3') b))
nf (Let x e1 e2) s k =
  nf e1 s (\a -> nf e2 (\y -> if y == x then a else s y) (return . EVal))
nf (LetRec f ((x, ty), e1) e2) s k = do
  a <- fresh
  let subst y = if y == f then AVar a else s y
  e1' <- nf e1 subst (return . EVal)
  e2' <- nf e2 subst (return . EVal)
  return (ELetRec a ((x, ty), e1') e2')
nf (Abs (x, ty) e) s k = do
  a <- fresh
  b <- nf e s (return . EVal)
  c <- k (AVar a)
  return (ELet a (CAbs (x, ty) b) c)
nf (App e1 e2) s k = nf e1 s (\e1' -> nf e2 s (\e2' -> do
  a <- fresh
  d <- k (AVar a)
  return (ELet a (CApp e1' e2') d)))

toNormalFormM :: Expr -> NameGen ExprNF
toNormalFormM e = nf e AVar (return . EVal)

toNormalForm :: Expr -> ExprNF
toNormalForm = runNameGen . toNormalFormM

-- Intermediate language in normal form with closures

data AtomicExprCl =
  ACLitInt Integer |
  ACLitBool Bool |
  ACExternVar Id |
  ACVar Id |
  ACVarSelf |
  ACVarEnv Integer

type Env = [AtomicExprCl]

data ComplexExprCl =
  CCOpAdd AtomicExprCl AtomicExprCl |
  CCOpSub AtomicExprCl AtomicExprCl |
  CCOpMul AtomicExprCl AtomicExprCl |
  CCOpDiv AtomicExprCl AtomicExprCl |
  CCOpLT AtomicExprCl AtomicExprCl |
  CCOpEQ AtomicExprCl AtomicExprCl |
  CCIf AtomicExprCl ExprNFCl ExprNFCl |
  CCApp AtomicExprCl AtomicExprCl |
  CCClosure (Id, Type) ExprNFCl Env

data ExprNFCl =
  ECVal AtomicExprCl |
  ECLet Id ComplexExprCl ExprNFCl

-- Pretty print

instance Show AtomicExprCl where
  show (ACLitInt n) = show n
  show (ACLitBool n) = show n
  show (ACExternVar x) = show x
  show (ACVar x) = x
  show (ACVarSelf) = "env.self"
  show (ACVarEnv n) = "env." ++ show n

instance Show ComplexExprCl where
  show (CCOpAdd e1 e2) = show e1 ++ " + " ++ show e2
  show (CCOpSub e1 e2) = show e1 ++ " - " ++ show e2
  show (CCOpMul e1 e2) = show e1 ++ " * " ++ show e2
  show (CCOpDiv e1 e2) = show e1 ++ " / " ++ show e2
  show (CCOpLT e1 e2) = show e1 ++ " < " ++ show e2
  show (CCOpEQ e1 e2) = show e1 ++ " = " ++ show e2
  show (CCIf e1 e2 e3) =
    "if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3
  show (CCApp e1 e2) = show e1 ++ " " ++ show e2
  show (CCClosure (x, ty) f env) =
    "Closure (fun env -> fun " ++ x ++ " : " ++ show ty ++ " -> " ++
      show f ++ ", " ++ show env ++ ")"

instance Show ExprNFCl where
  show (ECVal x) = show x
  show (ECLet x e1 e2) =
    "let " ++ x ++ " = " ++ show e1 ++ " in\n" ++ show e2

-- Normal form -> normal form with closure

class FreeVariables a where
  fv :: a -> [Id]

instance FreeVariables AtomicExpr where
  fv (ALitInt _) = []
  fv (ALitBool _) = []
  fv (AVar x) = [x]
  fv (AExternVar x) = []

instance FreeVariables ComplexExpr where
  fv (COpAdd e1 e2) = Data.List.union (fv e1) (fv e2)
  fv (COpSub e1 e2) = Data.List.union (fv e1) (fv e2)
  fv (COpMul e1 e2) = Data.List.union (fv e1) (fv e2)
  fv (COpDiv e1 e2) = Data.List.union (fv e1) (fv e2)
  fv (COpLT  e1 e2) = Data.List.union (fv e1) (fv e2)
  fv (COpEQ  e1 e2) = Data.List.union (fv e1) (fv e2)
  fv (CIf  b e1 e2) = let u = Data.List.union in (fv b) `u` (fv e1) `u` (fv e2)
  fv (CApp   e1 e2) = Data.List.union (fv e1) (fv e2)
  fv (CAbs (x, _) e) = fv e \\ [x]

instance FreeVariables ExprNF where
  fv (EVal x) = fv x
  fv (ELet x e1 e2) = Data.List.union (fv e1) (fv e2 \\ [x])
  fv (ELetRec f ((x, _), e1) e2) =
    Data.List.union (fv e1 \\ [f, x]) (fv e2 \\ [f])

clAt :: (Id -> AtomicExprCl) -> AtomicExpr -> AtomicExprCl
clAt s (ALitInt n) = ACLitInt n
clAt s (ALitBool b) = ACLitBool b
clAt s (AVar x) = s x
clAt s (AExternVar x) = (ACExternVar x)

clAbs s f ((x, ty), e) =
  let fvs = fv e \\ [f, x] in
  let subst y =
        if x == y then
          ACVar x
        else
          maybe (s y) (ACVarEnv . toInteger) (Data.List.elemIndex y fvs)
   in CCClosure (x, ty) (clExpr subst e) (map ACVar fvs)

clCo :: (Id -> AtomicExprCl) -> ComplexExpr -> ComplexExprCl
clCo s (COpAdd e1 e2) = CCOpAdd (clAt s e1) (clAt s e2)
clCo s (COpSub e1 e2) = CCOpSub (clAt s e1) (clAt s e2)
clCo s (COpMul e1 e2) = CCOpMul (clAt s e1) (clAt s e2)
clCo s (COpDiv e1 e2) = CCOpDiv (clAt s e1) (clAt s e2)
clCo s (COpLT  e1 e2) = CCOpLT  (clAt s e1) (clAt s e2)
clCo s (COpEQ  e1 e2) = CCOpEQ  (clAt s e1) (clAt s e2)
clCo s (CIf  b e1 e2) = CCIf (clAt s b) (clExpr s e1) (clExpr s e2)
clCo s (CApp   e1 e2) = CCApp   (clAt s e1) (clAt s e2)
clCo s (CAbs (x, ty) e) = clAbs s "" ((x, ty), e)

clExpr :: (Id -> AtomicExprCl) -> ExprNF -> ExprNFCl
clExpr s (EVal a) = ECVal (clAt s a)
clExpr s (ELet x e1 e2) = ECLet x (clCo s e1) (clExpr s e2)
clExpr s (ELetRec f ((x, ty), e1) e2) = ECLet f
    (clAbs (\g -> if g == f then ACVarSelf else s g) f ((x, ty), e1))
    (clExpr s e2)

toClosure :: ExprNF -> ExprNFCl
toClosure = clExpr ACVar
