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

extractTypeVars :: Context -> [String]
extractTypeVars =
  let extractVars (TVar x) = [x]
      extractVars (TFun t1 t2) = extractVars t1 ++ extractVars t2
      extractVars _ = []
   in Data.List.concat . map (extractVars . snd)

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

genFreshTVar :: Monad m => NameGenT m Type
genFreshTVar = fresh >>= (return . TVar)

unify :: Type -> Type -> Maybe Subst
unify (TVar x) t = Just (singletonSubst (x, t))
unify t (TVar x) = Just (singletonSubst (x, t))
unify (TFun t1 t2) (TFun t1' t2') = do
  s1 <- unify t1 t1'
  s2 <- unify (applyOnType s1 t2) (applyOnType s1 t2')
  Just (concatSubst s1 s2)
unify x y = if x == y then Just emptySubst else Nothing

infer :: Context -> Term -> Maybe (Subst, Type)
infer c e = runNameGenTWithout (extractTypeVars c) (impl c e)
  where cat = concatSubst
        app = applyOnContext

        checkBinOpElements
            :: Type    -- ^ The type of the left hand side
            -> Type    -- ^ The type of the right hand side
            -> Type    -- ^ The type of the resulting expression
            -> Context -- ^ Context in which the expressions are type-checked
            -> Term    -- ^ Left hand side expression
            -> Term    -- ^ Right hand side expression
            -> NameGenT Maybe (Subst, Type)
        checkBinOpElements t1 t2 t c e1 e2 = do
          (s1, tau1) <- impl c e1
          s1' <- lift (unify tau1 t1)
          let s1'' = s1 `cat` s1'
          (s2, tau2) <- impl (s1'' `app` c) e2
          s2' <- lift (unify tau2 t2)
          return (s1'' `cat` s2 `cat` s2', t)

        impl :: Context -> Term -> NameGenT Maybe (Subst, Type)
        impl c (Var x) = lift (fmap ((,) emptySubst) (lookupContext x c))
        impl c (Abs x e) = do
          alpha <- genFreshTVar
          (s, tau) <- impl (addContext (x, alpha) c) e
          return (s, TFun (applyOnType s alpha) tau)
        impl c (App e1 e2) = do
          (s1, tau1) <- impl c e1
          (s2, tau2) <- impl (s1 `app` c) e2
          beta <- genFreshTVar
          s3 <- lift $ unify (applyOnType s2 tau1) (TFun tau2 beta)
          return (s1 `cat` s2 `cat` s3, applyOnType s3 beta)
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
          (s, tau) <- impl c e
          if tau /= TBool then
            lift Nothing
          else do
            (theta1, tau1) <- impl (s `app` c) e1
            (theta2, tau2) <- impl (theta1 `app` s `app` c) e2
            theta3 <- lift $ unify (applyOnType theta2 tau1) tau2
            return (s `cat` theta1 `cat` theta2 `cat` theta3, applyOnType theta3 tau2)
        impl c (Let x e1 e2) = do
          (theta1, tau1) <- impl c e1
          (theta2, tau2) <- impl (addContext  (x, tau1) (theta1 `app` c)) e2
          return (theta1 `cat` theta2, tau2)
        impl c (LetRec x e1 e2) = do
          alpha <- genFreshTVar
          (theta1, tau1) <- impl (addContext (x, alpha) c) e1
          (theta2, tau2) <- impl (addContext (x, tau1) (theta1 `app` c)) e2
          return (theta1 `cat` theta2, tau2)
