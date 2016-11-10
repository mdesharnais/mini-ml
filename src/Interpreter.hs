module Interpreter where

import qualified Data.List

import Parser(Name(..), Constant(..), Term(..))

type Env = [(String, Value)]

data Value =
  VClosure String Term Env |
  VConst Constant [Value]
  deriving (Eq, Show)

valInt :: Integer -> Value
valInt n = VConst Constant { name = NInt n, arity = 0, constr = True } []

valBool :: Bool -> Value
valBool x = VConst Constant { name = NBool x, arity = 0, constr = True } []

valFix = VConst Constant { name = NString "fix", arity = 2, constr = False } []

getInt :: Value -> Maybe Integer
getInt (VConst (Constant (NInt n) _ _) []) = Just n
getInt _ = Nothing

getBool :: Value -> Maybe Bool
getBool (VConst (Constant (NBool x) _ _) []) = Just x
getBool _ = Nothing

deltaBinOp v1 v2 get val op =  do
  n1 <- get v1
  n2 <- get v2
  Just (val (op n1 n2))

delta :: Constant -> [Value] -> Maybe Value
delta (Constant (NString "+") 2 _) [v1, v2] = deltaBinOp v1 v2 getInt valInt (+)
delta (Constant (NString "-") 2 _) [v1, v2] = deltaBinOp v1 v2 getInt valInt (-)
delta (Constant (NString "*") 2 _) [v1, v2] = deltaBinOp v1 v2 getInt valInt (*)
delta (Constant (NString "/") 2 _) [v1, v2] = deltaBinOp v1 v2 getInt valInt quot
delta (Constant (NString "<") 2 _) [v1, v2] = deltaBinOp v1 v2 getInt valBool (<)
delta (Constant (NString "=") 2 _) [v1, v2] = deltaBinOp v1 v2 getInt valBool (==)
{-
delta (Constant (NString "fix") 2 _) [f, v] =
  case f of
    VClosure x t env -> Nothing
    _ -> Nothing
-}
delta _ _ = Nothing

evalBinOp env t1 t2 val op = do
  v1 <- eval env t1
  v2 <- eval env t2
  deltaBinOp v1 v2 getInt val op

eval :: Env -> Term -> Maybe Value
eval env (Var x) = Data.List.lookup x env
eval env (Abs x t) = Just (VClosure x t env)
eval env (App t1 t2) = do
  v1 <- eval env t1
  v2 <- eval env t2
  case v1 of
    VClosure x t env' -> eval ((x, v2) : env') t
    VConst c vs ->
      let k = toInteger (length vs + 1)
          a = arity c
       in if a < k then Nothing
          else if a > k then Just (VConst c (v2 : vs))
          else if constr c then Just (VConst c (v2 : vs))
          else delta c (v2 : vs)
eval env (LitInt n) = Just (valInt n)
eval env LitTrue = Just (valBool True)
eval env LitFalse = Just (valBool False)
eval env (OpMul t1 t2) = evalBinOp env t1 t2 valInt (*)
eval env (OpDiv t1 t2) = evalBinOp env t1 t2 valInt quot
eval env (OpAdd t1 t2) = evalBinOp env t1 t2 valInt (+)
eval env (OpSub t1 t2) = evalBinOp env t1 t2 valInt (-)
eval env (OpLT t1 t2) = evalBinOp env t1 t2 valBool (<)
eval env (OpEQ t1 t2) = evalBinOp env t1 t2 valBool (==)
eval env (If t1 t2 t3) = do
  v1 <- eval env t1
  case v1 of
    VConst (Constant (NBool True) _ _) [] -> eval env t2
    VConst (Constant (NBool False) _ _) [] -> eval env t3
    _ -> Nothing
eval env (Let x t1 t2) = do
  v1 <- eval env t1
  eval ((x, v1) : env) t2
eval env (LetRec x t1 t2) = undefined
