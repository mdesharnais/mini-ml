module Type where

import qualified Data.List
import qualified Data.Maybe

import Control.Monad.Trans(lift)
import FreshName
import Parser(Term(..))

data Type =
  TBool |
  TInt |
  TFun Type Type |
  TVar String
  deriving (Eq, Show)

type Context = [(String, Type)]

emptyContext :: Context
emptyContext = []

addContext :: (String, Type) -> Context -> Context
addContext = (:)

lookupContext :: String -> Context -> Maybe Type
lookupContext = Data.List.lookup

singletonContext :: (String, Type) -> Subst
singletonContext p = addContext p emptyContext

contextFromList :: [(String, Type)] -> Context
contextFromList = id

type Subst = [(String, Type)]

emptySubst :: Subst
emptySubst = []

addSubst :: (String, Type) -> Subst -> Subst
addSubst = (:)

singletonSubst :: (String, Type) -> Subst
singletonSubst p = addSubst p emptySubst

applyOnType :: Subst -> Type -> Type
applyOnType s (TFun t1 t2) = TFun (applyOnType s t1) (applyOnType s t2)
applyOnType s (TVar x) = Data.Maybe.fromMaybe (TVar x) (lookupContext x s)
applyOnType s t = t

applyOnContext :: Subst -> Context -> Context
applyOnContext s = map (\(x, ty) -> (x, applyOnType s ty))

concatSubst :: Subst -> Subst -> Subst
concatSubst = (++)

unify :: Type -> Type -> Maybe Subst
unify TInt TInt = Just emptySubst
unify TBool TBool = Just emptySubst
unify (TVar x) (TVar y) = if x == y then Just emptySubst else Nothing
unify (TVar x) t = Just (singletonSubst (x, t))
unify t (TVar x) = Just (singletonSubst (x, t))
unify (TFun t1 t2) (TFun t1' t2') =
  unify t1 t1' >>= \theta1 ->
    unify (applyOnType theta1 t2) (applyOnType theta1 t2') >>= \theta2 ->
      Just (concatSubst theta1 theta2)
unify _ _ = Nothing

infer :: Context -> Term -> Maybe (Subst, Type)
infer c e = runNameGenTWithout existingNames (impl c e)
  where extractVars (TVar x) = [x]
        extractVars (TFun t1 t2) = extractVars t1 ++ extractVars t2
        extractVars _ = []

        existingNames = Data.List.concat (map (extractVars . snd) c)

        checkBinOpElements
            :: Type    -- ^ The type of the left hand side
            -> Type    -- ^ The type of the right hand side
            -> Type    -- ^ The type of the resulting expression
            -> Context -- ^ Context in which the expressions are type-checked
            -> Term    -- ^ Left hand side expression
            -> Term    -- ^ Right hand side expression
            -> NameGenT Maybe (Subst, Type)
        checkBinOpElements t1 t2 t c e1 e2 = do
          (theta1, tau1) <- impl c e1
          case unify tau1 t1 of
            Just theta1' ->
              let theta1'' = concatSubst theta1 theta1'
               in do (theta2, tau2) <- impl (applyOnContext theta1'' c) e2
                     case unify tau2 t2 of
                       Just theta2' ->
                         let theta2'' = concatSubst theta2 theta2'
                          in return (concatSubst theta1'' theta2, t)
                       Nothing -> lift $ Nothing
            Nothing -> lift $ Nothing

        impl :: Context -> Term -> NameGenT Maybe (Subst, Type)
        impl c (Var x) = do
          case lookupContext x c of
            Just t -> return (emptySubst, t)
            Nothing -> lift Nothing
        impl c (Abs x e) = do
          name <- fresh
          let alpha = TVar name
          (theta, tau) <- impl (addContext (x, alpha) c) e
          return (theta, TFun (applyOnType theta alpha) tau)
        impl c (App e1 e2) = do
          (theta1, tau1) <- impl c e1
          (theta2, tau2) <- impl (applyOnContext theta1 c) e2
          name <- fresh
          let beta = TVar name
          theta3 <- lift $ unify (applyOnType theta2 tau1) (TFun tau2 beta)
          return (theta1 `concatSubst` theta2 `concatSubst` theta3, applyOnType theta3 beta)
        impl c (LitInt _) = return (emptySubst, TInt)
        impl c LitTrue = return (emptySubst, TBool)
        impl c LitFalse = return (emptySubst, TBool)
        impl c (OpMul e1 e2) = checkBinOpElements TInt TInt TInt c e1 e2
        impl c (OpDiv e1 e2) = checkBinOpElements TInt TInt TInt c e1 e2
        impl c (OpAdd e1 e2) = checkBinOpElements TInt TInt TInt c e1 e2
        impl c (OpSub e1 e2) = checkBinOpElements TInt TInt TInt c e1 e2
        impl c (OpLT e1 e2) = checkBinOpElements TInt TInt TBool c e1 e2
        impl c (OpEQ e1 e2) = checkBinOpElements TInt TInt TBool c e1 e2
        impl c (If e e1 e2) = do
          (theta, tau) <- impl c e
          if tau /= TBool then
            lift $ Nothing
          else do
            let c' = applyOnContext theta c
            (theta1, tau1) <- impl c' e1
            let c'' = applyOnContext theta1 c'
            (theta2, tau2) <- impl c'' e2
            theta3 <- lift $ unify (applyOnType theta2 tau1) tau2
            let cat = concatSubst
            return (theta `cat` theta1 `cat` theta2 `cat` theta3, applyOnType theta3 tau2)
        impl c (Let x e1 e2) = do
          (theta1, tau1) <- impl c e1
          (theta2, tau2) <- impl (addContext  (x, tau1) (applyOnContext theta1 c)) e2
          return (theta1 `concatSubst` theta2, tau2)
        impl c (LetRec x e1 e2) = do
          name <- fresh
          let alpha = TVar name
          (theta1, tau1) <- impl (addContext (x, alpha) c) e1
          (theta2, tau2) <- impl (addContext (x, tau1) (applyOnContext theta1 c)) e2
          return (theta1 `concatSubst` theta2, tau2)
