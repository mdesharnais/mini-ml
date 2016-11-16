module Test where

import FreshName

type Id = String

-- Source language
data Expr =
  ELit Integer |
  EVar Id |
  EPlus Expr Expr |
  ELet Id Expr Expr |
  EAbs Id Expr |
  EApp Expr Expr
  deriving (Show)

-- Intermediate language
data AtomicTerm =
  ATLit Integer |
  ATVar Id

data SimpleTerm =
  STPlus AtomicTerm AtomicTerm |
  STAbs Id Term |
  STApp AtomicTerm AtomicTerm

data Term =
  TVal AtomicTerm |
  TLet Id SimpleTerm Term

-- Pretty print
instance Show AtomicTerm where
  show (ATLit n) = show n
  show (ATVar x) = x

instance Show SimpleTerm where
  show (STPlus e1 e2) = show e1 ++ " + " ++ show e2
  show (STAbs x e) = "fun " ++ x ++ " -> " ++ show e
  show (STApp e1 e2) = show e1 ++ " " ++ show e2

instance Show Term where
  show (TVal x) = show x
  show (TLet x e1 e2) = "let " ++ x ++ " = " ++ show e1 ++ " in\n" ++ show e2

-- Normal form
nf :: Expr -> (Id -> AtomicTerm) -> (AtomicTerm -> NameGen Term) -> NameGen Term
nf (ELit n) s k = k (ATLit n)
nf (EVar x) s k = k (s x)
nf (EPlus e1 e2) s k = nf e1 s (\a -> nf e2 s (\b -> do
  c <- fresh
  d <- k (ATVar c)
  return (TLet c (STPlus a b) d)))
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
