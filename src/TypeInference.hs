module TypeInference where

import qualified Control.Monad
import qualified Data.List as List
import qualified Data.Maybe
import qualified Expr
import qualified TypeContext as Context
import qualified TypeSubstitution as Subst

import Control.Monad.Trans(lift)
import Data.Bifunctor(bimap)
import Data.List((\\))
import Expr(Expr(..))
import FreshName
import Type(TyExpr, Type(..), TypeSchema(..), freeVars)
import TypeContext(Context)
import TypeSubstitution(Subst)

genFreshTVar :: Monad m => NameGenT m Type
genFreshTVar = fresh >>= (return . TVar)

unify :: Type -> Type -> Maybe Subst
unify (TVar x) (TVar y) = Just $
  if x == y then Subst.empty else Subst.singleton (x, TVar y)
unify (TVar x) t =
  if List.elem x (freeVars t) then Nothing else Just (Subst.singleton (x, t))
unify t (TVar x) =
  if List.elem x (freeVars t) then Nothing else Just (Subst.singleton (x, t))
unify (TFun t1 t2) (TFun t1' t2') = do
  s1 <- unify t1 t1'
  s2 <- unify (Subst.applyTy s1 t2) (Subst.applyTy s1 t2')
  Just (Subst.concat s1 s2)
unify x y = if x == y then Just Subst.empty else Nothing

infer :: Context -> Expr () () -> Maybe (Subst, TyExpr)
infer c e = do
  case runNameGenTWithout (Context.extractTypeVars c) (impl c e) of
    Nothing -> Nothing
    Just (s, expr) ->
      Just (s, bimap (Subst.applyTySchema s) (Subst.applyTy s) expr)
  where cat = Subst.concat
        app = Subst.applyContext

        checkBinOpElements
          :: (Type -> TyExpr -> TyExpr -> TyExpr)  -- ^ The constructor
          -> Type       -- ^ The type of the left hand side
          -> Type       -- ^ The type of the right hand side
          -> Type       -- ^ The type of the resulting expression
          -> Context    -- ^ Context in which the expressions are type-checked
          -> Expr () () -- ^ Left hand side expression
          -> Expr () () -- ^ Right hand side expression
          -> NameGenT Maybe (Subst, TyExpr)
        checkBinOpElements con t1 t2 t c e1 e2 = do
          (s1, e1') <- impl c e1
          s1' <- lift (unify (Expr.getType e1') t1)
          let s1'' = s1 `cat` s1'
          (s2, e2') <- impl (s1'' `app` c) e2
          s2' <- lift (unify (Expr.getType e2') t2)
          return (s1'' `cat` s2 `cat` s2', con t e1' e2')

        impl :: Context -> Expr () () -> NameGenT Maybe (Subst, TyExpr)
        impl c (Var _ x) = do
          let instanciate :: Monad m => Subst -> TypeSchema -> NameGenT m Type
              instanciate s (TSType ty) = return (Subst.applyTy s ty)
              instanciate s (TSForall x tySchema) = do
                alpha <- genFreshTVar
                instanciate (Subst.add (x, alpha) s) tySchema
          tySchema <- lift (Context.lookup x c)
          alpha <- instanciate Subst.empty tySchema
          return (Subst.empty, Var alpha x)
        impl c (ExternVar _ x) = do
          return (Subst.empty, ExternVar (TFun TInt TInt) x)
        impl c (Abs _ x e) = do
          alpha <- genFreshTVar
          (s, e') <- impl (Context.addTy (x, alpha) c) e
          let tau = TFun (Subst.applyTy s alpha) (Expr.getType e')
          return (s, Abs tau x e')
        impl c (App _ e1 e2) = do
          (s1, e1') <- impl c e1
          (s2, e2') <- impl (s1 `app` c) e2
          beta <- genFreshTVar
          s3 <- lift $ unify
            (Subst.applyTy s2 (Expr.getType e1')) (TFun (Expr.getType e2') beta)
          return (s1 `cat` s2 `cat` s3,
            App (Subst.applyTy s3 beta) e1' e2')
        impl c (LitInt  _ n) = return (Subst.empty, LitInt TInt n)
        impl c (LitBool _ b) = return (Subst.empty, LitBool TBool b)
        impl c (OpMul _ e1 e2) = checkBinOpElements OpMul TInt TInt TInt  c e1 e2
        impl c (OpDiv _ e1 e2) = checkBinOpElements OpDiv TInt TInt TInt  c e1 e2
        impl c (OpAdd _ e1 e2) = checkBinOpElements OpAdd TInt TInt TInt  c e1 e2
        impl c (OpSub _ e1 e2) = checkBinOpElements OpSub TInt TInt TInt  c e1 e2
        impl c (OpLT  _ e1 e2) = checkBinOpElements OpLT  TInt TInt TBool c e1 e2
        impl c (OpEQ  _ e1 e2) = checkBinOpElements OpEQ  TInt TInt TBool c e1 e2
        impl c (If _ e e1 e2) = do
          (s1, e') <- impl c e
          s2 <- lift $ unify (Expr.getType e') TBool
          let s3 = s1 `cat` s2
          (theta1, e1') <- impl (s3 `app` c) e1
          (theta2, e2') <- impl ((theta1 `cat` s3) `app` c) e2
          let tau2 = Expr.getType e2'
          theta3 <- lift $ unify (Subst.applyTy theta2 (Expr.getType e1')) tau2
          return (s3 `cat` theta1 `cat` theta2 `cat` theta3,
            If (Subst.applyTy theta3 tau2) e' e1' e2')
        impl c (Let _ (x, _) e1 e2) = do
          (theta1, e1') <- impl c e1
          let theta1' = theta1 `app` c
          let tau1 = Expr.getType e1'
          let fv = freeVars tau1
          let tyVars = fv \\ (Context.extractTypeVars theta1')
          let tau1' = List.foldl (flip TSForall) (TSType tau1) tyVars
          (theta2, e2') <- impl (Context.add (x, tau1') theta1') e2
          return (theta1 `cat` theta2, Let (Expr.getType e2') (x, tau1') e1' e2')
        impl c (LetRec _ (f, _) (y, e1) e2) = do
          alpha <- genFreshTVar
          (theta1, a@(Abs tau1 _ e1')) <-
            impl (Context.addTy (f, alpha) c) (Abs () y e1)
          s <- lift (unify (Subst.applyTy theta1 alpha) tau1)
          let theta1' = theta1 `app` c
          let fv = freeVars tau1
          let tyVars = fv \\ (Context.extractTypeVars (s `app` theta1'))
          let tau1' = List.foldl (flip TSForall) (TSType tau1) tyVars
          (theta2, e2') <- impl (s `app` (Context.add (f, tau1') theta1')) e2
          return (theta1 `cat` s `cat` theta2, LetRec (Expr.getType e2') (f, tau1') (y, e1') e2')
