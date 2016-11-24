{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module Compiler where

import qualified Data.List

import Data.List((\\))
import Expr(Expr(..), Id)
import FreshName

-- Intermediate language in normal form

data AtomicExpr =
  ALitInt Integer |
  ALitBool Bool |
  AVar Id |
  AAbs Id (ExprNF AtomicExpr)

data ComplexExpr a =
  COpAdd a a |
  COpSub a a |
  COpMul a a |
  COpDiv a a |
  COpLT a a |
  COpEQ a a |
  CIf a (ExprNF a) (ExprNF a) |
  CApp a a
  deriving (Foldable, Functor)

data ExprNF a =
  EVal a |
  ELet Id (ComplexExpr a) (ExprNF a) |
  ELetRec Id (Id, ExprNF a) (ExprNF a)
  deriving (Foldable, Functor)

type ComplexExprAbs = ComplexExpr AtomicExpr
type ExprNFAbs = ExprNF AtomicExpr

-- Intermediate language in normal form with closures

type Env = [AtomicExprClosure]

data AtomicExprClosure =
  ACLitInt Integer |
  ACLitBool Bool |
  ACVar Id |
  ACVarN Integer |
  ACClosure Id ExprNFClosure Env

type ComplexExprClosure = ComplexExpr AtomicExprClosure
type ExprNFClosure = ExprNF AtomicExprClosure

-- Pretty print

instance Show AtomicExpr where
  show (ALitInt n) = show n
  show (ALitBool n) = show n
  show (AVar x) = x
  show (AAbs x e) = "(fun " ++ x ++ " -> " ++ show e ++ ")"

instance Show AtomicExprClosure where
  show (ACLitInt n) = show n
  show (ACLitBool n) = show n
  show (ACVar x) = x
  show (ACVarN n) = "env." ++ show n
  show (ACClosure x f env) =
    "Closure (fun env -> fun " ++ x ++ " -> " ++ show f ++ ", " ++ show env ++ ")"

instance Show a => Show (ComplexExpr a) where
  show (COpAdd e1 e2) = show e1 ++ " + " ++ show e2
  show (COpSub e1 e2) = show e1 ++ " - " ++ show e2
  show (COpMul e1 e2) = show e1 ++ " * " ++ show e2
  show (COpDiv e1 e2) = show e1 ++ " / " ++ show e2
  show (COpLT e1 e2) = show e1 ++ " < " ++ show e2
  show (COpEQ e1 e2) = show e1 ++ " = " ++ show e2
  show (CIf e1 e2 e3) =
    "if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3
  show (CApp e1 e2) = show e1 ++ " " ++ show e2

instance Show a => Show (ExprNF a) where
  show (EVal x) = show x
  show (ELet x e1 e2) =
    "let " ++ x ++ " = " ++ show e1 ++ " in\n" ++ show e2
  show (ELetRec x (y, e1) e2) =
    "let rec " ++ x ++ " = (fun " ++ y ++ " -> " ++ show e1 ++ ") in\n" ++ show e2

-- Expression -> normal form

nfBinOp :: Expr -> Expr -> (AtomicExpr -> AtomicExpr -> ComplexExprAbs) ->
  (Id -> AtomicExpr) -> (AtomicExpr -> NameGen ExprNFAbs) -> NameGen ExprNFAbs
nfBinOp e1 e2 op s k = nf e1 s (\a -> nf e2 s (\b -> do
  c <- fresh
  d <- k (AVar c)
  return (ELet c (op a b) d)))

nf :: Expr ->
  (Id -> AtomicExpr) ->
  (AtomicExpr -> NameGen ExprNFAbs) ->
  NameGen ExprNFAbs
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
  a <- fresh
  e2' <- nf e2 s (return . EVal)
  e3' <- nf e3 s (return . EVal)
  b <- k (AVar a)
  return (ELet a (CIf e1' e2' e3') b))
nf (Let x e1 e2) s k =
  nf e1 s (\a -> nf e2 (\y -> if y == x then a else s y) (return . EVal))
nf (LetRec x (y, e1) e2) s k = do
  a <- fresh
  e1' <- nf e1 s (return . EVal)
  e2' <- nf e2 (\z -> if z == x then AVar a else s z) (return . EVal)
  return (ELetRec a (y, e1') e2')
nf (Abs x e) s k = do
  b <- nf e s (return . EVal)
  k (AAbs x b)
nf (App e1 e2) s k = nf e1 s (\e1' -> nf e2 s (\e2' -> do
  a <- fresh
  d <- k (AVar a)
  return (ELet a (CApp e1' e2') d)))

toNormalFormM :: Expr -> NameGen ExprNFAbs
toNormalFormM e = nf e AVar (return . EVal)

toNormalForm :: Expr -> ExprNFAbs
toNormalForm = runNameGen . toNormalFormM

-- Normal form -> normal form with closure

class FreeVariables a where
  fv :: a -> [Id]

instance FreeVariables AtomicExpr where
  fv (ALitInt _) = []
  fv (ALitBool _) = []
  fv (AVar x) = [x]
  fv (AAbs x e) = fv e \\ [x]

instance FreeVariables a => FreeVariables (ComplexExpr a) where
  fv = foldl (\acc atExpr -> acc ++ fv atExpr) []

instance FreeVariables a => FreeVariables (ExprNF a) where
  fv (EVal x) = fv x
  fv (ELet x e1 e2) = fv e1 ++ (fv e2 \\ [x])
  fv (ELetRec f (x, e1) e2) = (fv e1 \\ [f, x]) ++ fv e2

cl :: (Id -> AtomicExprClosure) -> AtomicExpr -> AtomicExprClosure
cl s (ALitInt n) = ACLitInt n
cl s (ALitBool b) = ACLitBool b
cl s (AVar x) = s x
cl s (AAbs x e) =
  let fvs = fv (AAbs x e)
      subst = \y ->
        if x == y then
          ACVar x
        else maybe (ACVar y) (ACVarN . toInteger) (Data.List.elemIndex y fvs)
   in ACClosure x (fmap (cl subst) e) (map ACVar fvs)

toClosure :: ExprNFAbs -> ExprNFClosure
toClosure = fmap (cl ACVar)
