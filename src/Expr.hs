module Expr where

type Id = String

data Expr =
  LitInt Integer |
  LitBool Bool |
  Var Id |
  OpAdd Expr Expr |
  OpSub Expr Expr |
  OpMul Expr Expr |
  OpDiv Expr Expr |
  OpLT Expr Expr |
  OpEQ Expr Expr |
  If Expr Expr Expr |
  Let Id Expr Expr |
  LetRec Id (Id, Expr) Expr |
  Abs Id Expr |
  App Expr Expr
  deriving (Eq)

instance Show Expr where
  show (LitInt n) = show n
  show (LitBool b) = show b
  show (Var x) = x
  show (OpAdd e1 e2) = "(" ++ show e1 ++ " + " ++ show e2 ++ ")"
  show (OpSub e1 e2) = "(" ++ show e1 ++ " - " ++ show e2 ++ ")"
  show (OpMul e1 e2) = "(" ++ show e1 ++ " * " ++ show e2 ++ ")"
  show (OpDiv e1 e2) = "(" ++ show e1 ++ " / " ++ show e2 ++ ")"
  show (OpLT e1 e2)  = "(" ++ show e1 ++ " < " ++ show e2 ++ ")"
  show (OpEQ e1 e2)  = "(" ++ show e1 ++ " = " ++ show e2 ++ ")"
  show (If e1 e2 e3) =
    "if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3
  show (Let x e1 e2) =
    "let " ++ x ++ " = " ++ show e1 ++ " in " ++ show e2
  show (LetRec f (x, e1) e2) =
    "let rec " ++ f ++ " = fun " ++ x ++ " -> " ++ show e1 ++ " in " ++ show e2
  show (Abs x e1) = "(fun " ++ x ++ " -> " ++ show e1 ++ ")"
  show (App e1 e2) = show e1 ++ " " ++ show e2
