{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ForeignFunctionInterface #-}
module Interpreter where

import qualified Data.List

import Expr(Expr(..))
import Foreign
import Foreign.C.Types

foreign import ccall "printheader" c_printheader :: CLong -> CLong
foreign import ccall "printdot"    c_printdot    :: CLong -> CLong
foreign import ccall "impl1"       c_impl1       :: CLong -> CLong
foreign import ccall "impl2"       c_impl2       :: CLong -> CLong

externalFunctions :: [(String, CLong -> CLong)]
externalFunctions = [
    ("printheader", c_printheader),
    ("printdot",    c_printdot),
    ("impl1",       c_impl1),
    ("impl2",       c_impl2)
  ]

type Env tySch ty = [(String, Value tySch ty)]
data Value tySch ty =
  Closure String (Expr tySch ty) (Env tySch ty) |
  ConstInt Integer |
  ConstBool Bool
  deriving (Eq, Show)

evalBinOpInt env t1 t2 result f = do
  v1 <- eval env t1
  v2 <- eval env t2
  case (v1, v2) of
    (ConstInt n1, ConstInt n2) -> Just (result (f n1 n2))
    _ -> Nothing

eval :: Env tySch ty -> Expr tySch ty -> Maybe (Value tySch ty)
eval env (Var _ x) = Data.List.lookup x env
eval env (Abs _ x t) = Just (Closure x t env)
eval env abs@(AbsRec _ f x t) =
  let closure = Closure x t ((f, closure) : env) in Just closure
eval env (App _ (ExternVar _ f) t2) = do
  v2 <- eval env t2
  case v2 of
    (ConstInt n) -> do
      !fun <- Data.List.lookup f externalFunctions
      let !n' =  fun (fromInteger n)
      return (ConstInt (toInteger n'))
    _ -> Nothing
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
eval env (Let _ (x, _) t1 t2) = do
  v1 <- eval env t1
  eval ((x, v1) : env) t2
