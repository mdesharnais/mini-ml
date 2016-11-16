module Test where

import FreshName

type Id = String

-- Source language
data Expr =
  ELitInt Integer |
  ELitBool Bool |
  EVar Id |
  EOpAdd Expr Expr |
  EOpSub Expr Expr |
  EOpMul Expr Expr |
  EOpDiv Expr Expr |
  EOpLT Expr Expr |
  EOpEQ Expr Expr |
  EIf Expr Expr Expr |
  ELet Id Expr Expr |
  EAbs Id Expr |
  EApp Expr Expr
  deriving (Show)

-- Intermediate language
data AtomicTerm =
  ATLitInt Integer |
  ATLitBool Bool |
  ATVar Id

data SimpleTerm =
  STOpAdd AtomicTerm AtomicTerm |
  STOpSub AtomicTerm AtomicTerm |
  STOpMul AtomicTerm AtomicTerm |
  STOpDiv AtomicTerm AtomicTerm |
  STOpLT AtomicTerm AtomicTerm |
  STOpEQ AtomicTerm AtomicTerm |
  STIf AtomicTerm Term Term |
  STAbs Id Term |
  STApp AtomicTerm AtomicTerm

data Term =
  TVal AtomicTerm |
  TLet Id SimpleTerm Term

-- Pretty print
instance Show AtomicTerm where
  show (ATLitInt n) = show n
  show (ATLitBool n) = show n
  show (ATVar x) = x

instance Show SimpleTerm where
  show (STOpAdd e1 e2) = show e1 ++ " + " ++ show e2
  show (STOpSub e1 e2) = show e1 ++ " - " ++ show e2
  show (STOpMul e1 e2) = show e1 ++ " * " ++ show e2
  show (STOpDiv e1 e2) = show e1 ++ " / " ++ show e2
  show (STOpLT e1 e2) = show e1 ++ " < " ++ show e2
  show (STOpEQ e1 e2) = show e1 ++ " = " ++ show e2
  show (STIf e1 e2 e3) =
    "if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3
  show (STAbs x e) = "fun " ++ x ++ " -> " ++ show e
  show (STApp e1 e2) = show e1 ++ " " ++ show e2

instance Show Term where
  show (TVal x) = show x
  show (TLet x e1 e2) = "let " ++ x ++ " = " ++ show e1 ++ " in\n" ++ show e2

-- Normal form

nfBinOp :: Expr -> Expr -> (AtomicTerm -> AtomicTerm -> SimpleTerm) ->
  (Id -> AtomicTerm) -> (AtomicTerm -> NameGen Term) -> NameGen Term
nfBinOp e1 e2 op s k = nf e1 s (\a -> nf e2 s (\b -> do
  c <- fresh
  d <- k (ATVar c)
  return (TLet c (op a b) d)))

nf :: Expr -> (Id -> AtomicTerm) -> (AtomicTerm -> NameGen Term) -> NameGen Term
nf (ELitInt n) s k = k (ATLitInt n)
nf (ELitBool b) s k = k (ATLitBool b)
nf (EVar x) s k = k (s x)
nf (EOpAdd e1 e2) s k = nfBinOp e1 e2 STOpAdd s k
nf (EOpSub e1 e2) s k = nfBinOp e1 e2 STOpSub s k
nf (EOpMul e1 e2) s k = nfBinOp e1 e2 STOpMul s k
nf (EOpDiv e1 e2) s k = nfBinOp e1 e2 STOpDiv s k
nf (EOpLT e1 e2) s k = nfBinOp e1 e2 STOpLT s k
nf (EOpEQ e1 e2) s k = nfBinOp e1 e2 STOpEQ s k
nf (EIf e1 e2 e3) s k = nf e1 s (\e1' -> do
  e2' <- nf e2 s (return . TVal)
  e3' <- nf e3 s (return . TVal)
  a <- fresh
  b <- k (ATVar a)
  return (TLet a (STIf e1' e2' e3') b))
nf (ELet x e1 e2) s k = nf e1 s (\a -> nf e2 (\y -> if y == x then a else ATVar y) (return . TVal))
nf (EAbs x e) s k = do
  a <- fresh
  b <- nf e s (return . TVal)
  c <- k (ATVar a)
  return (TLet a (STAbs x b) c)
nf (EApp e1 e2) s k = nf e1 s (\a -> nf e2 s (\b -> do
  c <- fresh
  d <- k (ATVar c)
  return (TLet c (STApp a b) d)))

toNormalForm :: Expr -> Term
toNormalForm e = runNameGen (nf e ATVar (return . TVal))
