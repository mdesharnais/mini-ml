module Type where

import Parser(Term(..))

data Type =
  TBool |
  TInt |
  TFun Type Type |
  TVar String
  deriving (Eq, Show)

type Context = String -> Type

extendContext :: Context -> String -> Type -> Context
extendContext c s t = \x -> if x == s then t else c s

type Subst = Type -> Type

concat :: Subst -> Subst -> Subst
concat a b = b . a

apply :: Subst -> Context -> Context
apply s c = s . c

unify :: Type -> Type -> Maybe Subst
unify TInt TInt = Just id
unify TBool TBool = Just id
unify (TVar x) (TVar y) = if x == y then Just id else Nothing
unify (TVar x) t = Just (\t2 -> case t2 of
    TVar y -> if x == y then t else t2
    _ -> t2)
unify t (TVar x) = Just (\t2 -> case t2 of
    TVar y -> if x == y then t else t2
    _ -> t2)
unify (TFun t1 t2) (TFun t1' t2') =
  unify t1 t1' >>= \theta1 ->
    unify (theta1 t2) (theta1 t2') >>= \theta2 ->
      Just (Type.concat theta1 theta2)
unify _ _ = Nothing

checkBinOpElements :: Type -> Context -> Term -> Term -> Maybe (Subst, Type)
checkBinOpElements t c e1 e2 = do
  (theta1, tau1) <- infer c e1
  if tau1 == t then
    do (theta2, tau2) <- infer (apply theta1 c) e2
       if tau2 == t then
         Just (Type.concat theta1 theta2, TInt)
       else
         Nothing
  else
    Nothing

infer :: Context -> Term -> Maybe (Subst, Type)
infer c (Var x) = Just (id, c x)
infer c (Abs x e) = do
  let alpha = TVar "alpha"
  (theta, tau) <- infer (extendContext c x alpha) e
  return (theta, TFun (theta alpha) tau)
infer c (App e1 e2) = do
  (theta1, tau1) <- infer c e1
  (theta2, tau2) <- infer (apply theta1 c) e2
  let beta = TVar "beta"
  theta3 <- unify (theta2 tau1) (TFun tau2 beta)
  return (theta1 `Type.concat` theta2 `Type.concat` theta3, theta3 beta)
infer c (LitInt _) = Just (id, TInt)
infer c LitTrue = Just (id, TBool)
infer c LitFalse = Just (id, TBool)
infer c (OpMul e1 e2) = checkBinOpElements TInt c e1 e2
infer c (OpDiv e1 e2) = checkBinOpElements TInt c e1 e2
infer c (OpAdd e1 e2) = checkBinOpElements TInt c e1 e2
infer c (OpSub e1 e2) = checkBinOpElements TInt c e1 e2
infer c (OpLT e1 e2) = checkBinOpElements TInt c e1 e2
infer c (OpEQ e1 e2) = checkBinOpElements TInt c e1 e2
infer c (If e e1 e2) = do
  (theta, tau) <- infer c e
  if tau /= TBool then
    Nothing
  else do
    let c' = apply theta c
    (theta1, tau1) <- infer c' e1
    let c'' = apply theta1 c'
    (theta2, tau2) <- infer c'' e2
    theta3 <- unify (theta2 tau1) tau2
    let cat = Type.concat
    return (theta `cat` theta1 `cat` theta2 `cat` theta3, theta3 tau2)
infer c (Let x e1 e2) = do
  (theta1, tau1) <- infer c e1
  (theta2, tau2) <- infer (extendContext (apply theta1 c) x tau1) e2
  return (theta1 `Type.concat` theta2, tau2)
infer c (LetRec x e1 e2) = do
  let alpha = TVar "alpha"
  (theta1, tau1) <- infer (extendContext c x alpha) e1
  (theta2, tau2) <- infer (extendContext (apply theta1 c) x tau1) e2
  return (theta1 `Type.concat` theta2, tau2)
