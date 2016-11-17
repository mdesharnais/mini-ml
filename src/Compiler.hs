module Compiler where

import Expr(Expr(..), Id)
import FreshName

-- Intermediate language in normal form
data AtomicExpr =
  ALitInt Integer |
  ALitBool Bool |
  AVar Id |
  AAbs Id ExprNF

data ComplexExpr =
  COpAdd AtomicExpr AtomicExpr |
  COpSub AtomicExpr AtomicExpr |
  COpMul AtomicExpr AtomicExpr |
  COpDiv AtomicExpr AtomicExpr |
  COpLT AtomicExpr AtomicExpr |
  COpEQ AtomicExpr AtomicExpr |
  CIf AtomicExpr ExprNF ExprNF |
  CApp AtomicExpr AtomicExpr

data ExprNF =
  EVal AtomicExpr |
  ELet Id ComplexExpr ExprNF |
  ELetRec Id (Id, ExprNF) ExprNF

-- Pretty print
instance Show AtomicExpr where
  show (ALitInt n) = show n
  show (ALitBool n) = show n
  show (AVar x) = x
  show (AAbs x e) = "(fun " ++ x ++ " -> " ++ show e ++ ")"

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

instance Show ExprNF where
  show (EVal x) = show x
  show (ELet x e1 e2) =
    "let " ++ x ++ " = " ++ show e1 ++ " in\n" ++ show e2
  show (ELetRec x (y, e1) e2) =
    "let rec " ++ x ++ " = " ++ show (AAbs y e1) ++ " in\n" ++ show e2

-- Normal form
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
nf (OpAdd e1 e2) s k = nfBinOp e1 e2 COpAdd s k
nf (OpSub e1 e2) s k = nfBinOp e1 e2 COpSub s k
nf (OpMul e1 e2) s k = nfBinOp e1 e2 COpMul s k
nf (OpDiv e1 e2) s k = nfBinOp e1 e2 COpDiv s k
nf (OpLT e1 e2) s k = nfBinOp e1 e2 COpLT s k
nf (OpEQ e1 e2) s k = nfBinOp e1 e2 COpEQ s k
nf (If e1 e2 e3) s k = nf e1 s (\e1' -> do
  e2' <- nf e2 s (return . EVal)
  e3' <- nf e3 s (return . EVal)
  a <- fresh
  b <- k (AVar a)
  return (ELet a (CIf e1' e2' e3') b))
nf (Let x e1 e2) s k =
  nf e1 s (\a -> nf e2 (\y -> if y == x then a else AVar y) (return . EVal))
nf (LetRec x (y, e1) e2) s k = do
  e1' <- nf e1 s (return . EVal)
  a <- fresh
  e2' <- nf e2 (\z -> AVar (if z == x then a else z)) (return . EVal)
  return (ELetRec a (y, e1') e2')
nf (Abs x e) s k = do
  b <- nf e s (return . EVal)
  k (AAbs x b)
nf (App e1 e2) s k = nf e1 s (\a -> nf e2 s (\b -> do
  c <- fresh
  d <- k (AVar c)
  return (ELet c (CApp a b) d)))

toNormalForm :: Expr -> ExprNF
toNormalForm e = runNameGen (nf e AVar (return . EVal))
