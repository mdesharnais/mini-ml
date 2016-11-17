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
  deriving (Eq, Show)
