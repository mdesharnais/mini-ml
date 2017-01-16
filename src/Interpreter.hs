module Interpreter where

import qualified Data.List

import Expr(Expr(..))

type Env ty = [(String, Value ty)]
data Value ty =
  Closure String (Expr ty) (Env ty) |
  ConstInt Integer |
  ConstBool Bool
  deriving (Eq, Show)

evalBinOpInt env t1 t2 result f = do
  v1 <- eval env t1
  v2 <- eval env t2
  case (v1, v2) of
    (ConstInt n1, ConstInt n2) -> Just (result (f n1 n2))
    _ -> Nothing

eval :: Env ty -> Expr ty -> Maybe (Value ty)
eval env (Var _ x) = Data.List.lookup x env
eval env (Abs _ x t) = Just (Closure x t env)
eval env (App _ t1 t2) = do
  v1 <- eval env t1
  v2 <- eval env t2
  case v1 of
    Closure x t env' -> eval ((x, v2) : env') t
    _ -> Nothing
eval env (LitInt  _ n) = Just (ConstInt n)
eval env (LitBool _ b) = Just (ConstBool b)
eval env (OpMul _ t1 t2) = evalBinOpInt env t1 t2 ConstInt (*)
eval env (OpDiv _ t1 t2) = evalBinOpInt env t1 t2 ConstInt quot
eval env (OpAdd _ t1 t2) = evalBinOpInt env t1 t2 ConstInt (+)
eval env (OpSub _ t1 t2) = evalBinOpInt env t1 t2 ConstInt (-)
eval env (OpLT  _ t1 t2) = evalBinOpInt env t1 t2 ConstBool (<)
eval env (OpEQ  _ t1 t2) = evalBinOpInt env t1 t2 ConstBool (==)
eval env (If _ t1 t2 t3) = do
  v1 <- eval env t1
  case v1 of
    ConstBool True -> eval env t2
    ConstBool False -> eval env t3
    _ -> Nothing
eval env (Let _ x t1 t2) = do
  v1 <- eval env t1
  eval ((x, v1) : env) t2
eval env (LetRec ty f (ty2, x, t1) t2) =
  let closure = Closure x (LetRec ty f (ty2, x, t1) t1) env
   in eval ((f, closure) : env) t2
