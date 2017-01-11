module Interpreter where

import qualified Data.List

import Expr(TyExpr(..), Expr)

type Env = [(String, Value)]
data Value =
  Closure String Expr Env |
  ConstInt Integer |
  ConstBool Bool
  deriving (Eq, Show)

evalBinOpInt env t1 t2 result f = do
  v1 <- eval env t1
  v2 <- eval env t2
  case (v1, v2) of
    (ConstInt n1, ConstInt n2) -> Just (result (f n1 n2))
    _ -> Nothing

eval :: Env -> Expr -> Maybe Value
eval env (Var x) = Data.List.lookup x env
eval env (Abs (x, _) t) = Just (Closure x t env)
eval env (App t1 t2) = do
  v1 <- eval env t1
  v2 <- eval env t2
  case v1 of
    Closure x t env' -> eval ((x, v2) : env') t
    _ -> Nothing
eval env (LitInt n) = Just (ConstInt n)
eval env (LitBool b) = Just (ConstBool b)
eval env (OpMul t1 t2) = evalBinOpInt env t1 t2 ConstInt (*)
eval env (OpDiv t1 t2) = evalBinOpInt env t1 t2 ConstInt quot
eval env (OpAdd t1 t2) = evalBinOpInt env t1 t2 ConstInt (+)
eval env (OpSub t1 t2) = evalBinOpInt env t1 t2 ConstInt (-)
eval env (OpLT t1 t2) = evalBinOpInt env t1 t2 ConstBool (<)
eval env (OpEQ t1 t2) = evalBinOpInt env t1 t2 ConstBool (==)
eval env (If t1 t2 t3) = do
  v1 <- eval env t1
  case v1 of
    ConstBool True -> eval env t2
    ConstBool False -> eval env t3
    _ -> Nothing
eval env (Let x t1 t2) = do
  v1 <- eval env t1
  eval ((x, v1) : env) t2
eval env (LetRec f ((x, ty), t1) t2) =
  let closure = Closure x (LetRec f ((x, ty), t1) t1) env
   in eval ((f, closure) : env) t2
