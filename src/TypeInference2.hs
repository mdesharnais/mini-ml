{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module TypeInference2 where

import qualified Data.List as List
import qualified Data.Set as Set
import qualified TypeSubstitution as Subst
import qualified TypeContext as Context

import Control.Monad((<=<))
import Control.Monad.Trans(lift)
import Data.Bifunctor(bimap)
import Data.List((\\))
import Data.Set(Set)
import Expr
import FreshName
import Type
import TypeContext(Context)
import TypeSubstitution(Subst)

occursIn x ty =
  case ty of
    TInt -> False
    TBool -> False
    (TFun _ t1 t2) -> occursIn x t1 || occursIn x t2
    (TVar y) -> x == y

unify :: Type -> Type -> Maybe Subst
unify TInt TInt = return Subst.empty
unify TBool TBool = return Subst.empty
unify (TFun b t1 t2) (TFun b' t1' t2') = do
  let app = Subst.applyTy
  let o = Subst.comp
  s0 <- return (Subst.singletonAn b' b)
  s1 <- unify (app s0 t1) (app s0 t1')
  s2 <- unify (app s1 (app s0 t2)) (app s1 (app s0 t2'))
  return (s2 `o` s1 `o` s0)
unify t alpha@(TVar x) =
  if t == alpha || not (occursIn x t) then
    return (Subst.singletonTy x t)
  else
    Nothing
unify alpha@(TVar x) t = unify t alpha
unify t1 t2 = Nothing

-- Constraints (Principles of Program Analysis, p. 308)

newtype Constraint = Constraint (AnVar, SAnn ()) deriving (Eq, Ord)

substApplyConstraint :: Subst -> Constraint -> Constraint
substApplyConstraint s (Constraint (x, ann)) =
  Constraint (Subst.applyAn s x, ann)

substApplyConstraints :: Subst -> Set Constraint -> Set Constraint
substApplyConstraints = Set.map . substApplyConstraint

-- The algorithm (Principles of Program Analysis, p. 309)

freshSTVar :: Monad m => NameGenT m Type
freshSTVar = fmap TVar fresh

freshAVar :: Monad m => NameGenT m AnVar
freshAVar = fresh

checkBinOp
  :: (Type -> TyExpr -> TyExpr -> TyExpr)  -- ^ The constructor
  -> Type       -- ^ The type of the left hand side
  -> Type       -- ^ The type of the right hand side
  -> Type       -- ^ The type of the resulting expression
  -> Context    -- ^ Context in which the expressions are type-checked
  -> Expr () () -- ^ Left hand side expression
  -> Expr () () -- ^ Right hand side expression
  -> NameGenT Maybe (TyExpr, Subst, Set Constraint)
checkBinOp con t1 t2 t c e1 e2 = do
  (e1', s1, cs1) <- inferImpl c e1
  (e2', s2, cs2) <- inferImpl c e2
  let e1Ty = Expr.getType e1'
  let e2Ty = Expr.getType e2'
  s3 <- lift (unify (Subst.applyTy s2 e1Ty) t1)
  s4 <- lift (unify (Subst.applyTy s3 e2Ty) t2)
  let o = Subst.comp
  let substs = s4 `o` s3 `o` s2 `o` s1
  let app = substApplyConstraints
  let cs = Set.union
        (s4 `app` (s3 `app` (s2 `app` (s1 `app` cs1))))
        (s4 `app` (s3 `app` cs1))
  return (con t e1' e2', substs, cs)

inferImpl :: Context -> Expr () ()
  -> NameGenT Maybe (TyExpr, Subst, Set Constraint)
inferImpl c (LitInt _ n) = return (LitInt TInt n, Subst.empty, Set.empty)
inferImpl c (LitBool _ b) = return (LitBool TBool b, Subst.empty, Set.empty)
inferImpl c (Var _ x) = do
  let instanciate :: Monad m => Subst -> TypeSchema -> NameGenT m Type
      instanciate s (TSType ty) = return (Subst.applyTy s ty)
      instanciate s (TSForall x tySch) = do
        alpha <- freshSTVar
        instanciate (Subst.comp s (Subst.singletonTy x alpha)) tySch
  tySch <- lift (List.lookup x c)
  alpha <- instanciate Subst.empty tySch
  return (Var alpha x, Subst.empty, Set.empty)
inferImpl c (ExternVar _ x) = do
  beta <- freshAVar
  let c = Constraint (beta, SAEmpty)
  return (ExternVar (TFun beta TInt TInt) x, Subst.empty, Set.singleton c)
inferImpl c (Abs _ x e) = do
  alpha <- freshSTVar
  (e', s, cs) <- inferImpl ((x, TSType alpha) : c) e
  beta <- freshAVar
  let ty = TFun beta (Subst.applyTy s alpha) (Expr.getType e')
  let cs' = Set.insert (Constraint (beta, SAEmpty)) cs
  return (Abs ty x e', s, cs')
inferImpl c (App _ e1 e2) = do
  (e1', s1, cs1) <- inferImpl c e1
  (e2', s2, cs2) <- inferImpl (Subst.applyContext s1 c) e2
  alpha <- freshSTVar
  beta <- freshAVar
  s3 <- lift $ unify
    (Subst.applyTy s2 (Expr.getType e1')) (TFun beta (Expr.getType e2') alpha)
  let app = substApplyConstraints
  let o = Subst.comp
  let cs = Set.union (app s3 (app s2 cs1)) (app s3 cs2)
  return (App (Subst.applyTy s3 alpha) e1' e2', s3 `o` (s2 `o` s1), cs)
inferImpl c (If _ e0 e1 e2) = do
  (e0', s0, cs0) <- inferImpl c e0
  let c2 = Subst.applyContext s0 c
  (e1', s1, cs1) <- inferImpl c2 e1
  let c3 = Subst.applyContext s1 c2
  (e2', s2, cs2) <- inferImpl c3 e2
  let ty0 = Expr.getType e0'
  let ty1 = Expr.getType e1'
  let ty2 = Expr.getType e2'
  s3 <- lift $ unify (Subst.applyTy s2 (Subst.applyTy s1 ty0)) TBool
  s4 <- lift $ unify (Subst.applyTy s3 ty1) (Subst.applyTy s3 (Subst.applyTy s2 ty2))
  let ty = Subst.applyTy s4 (Subst.applyTy s3 ty2)
  let o = Subst.comp
  let s = s4 `o` s3 `o` s2 `o` s1
  let app = substApplyConstraints
  let cs0' = s4 `app` (s3 `app` (s2 `app` (s1 `app` cs0)))
  let cs1' = s4 `app` (s3 `app` (s2 `app` cs1))
  let cs2' = s4 `app` (s3 `app` cs2)
  let cs = cs0' `Set.union` cs1' `Set.union` cs2'
  return (If ty e0' e1' e2', s, cs)
inferImpl c (Let _ (x, _) e1 e2) = do
  (e1', s1, cs1) <- inferImpl c e1
  let ty1 = Expr.getType e1'
  let c' = Subst.applyContext s1 c
  let tyVars = (freeVars ty1) \\ (Context.extractTypeVars c')
  let ty1' = List.foldl (flip TSForall) (TSType ty1) tyVars
  (e2', s2, cs2) <- inferImpl ((x, ty1') : Subst.applyContext s1 c) e2
  let ty2 = Expr.getType e2'
  let substs = Subst.comp s2 s1
  let cs = Set.union (substApplyConstraints s2 cs1) cs2
  return (Let ty2 (x, ty1') e1' e2', substs, cs)
inferImpl c (OpMul _ e1 e2) = checkBinOp OpMul TInt TInt TInt  c e1 e2
inferImpl c (OpDiv _ e1 e2) = checkBinOp OpDiv TInt TInt TInt  c e1 e2
inferImpl c (OpAdd _ e1 e2) = checkBinOp OpAdd TInt TInt TInt  c e1 e2
inferImpl c (OpSub _ e1 e2) = checkBinOp OpSub TInt TInt TInt  c e1 e2
inferImpl c (OpLT  _ e1 e2) = checkBinOp OpLT  TInt TInt TBool c e1 e2
inferImpl c (OpEQ  _ e1 e2) = checkBinOp OpEQ  TInt TInt TBool c e1 e2

infer :: Context -> Expr () () -> Maybe (Subst, TyExpr)
infer c e = do
  case runNameGenTWithout (Context.extractTypeVars c) (inferImpl c e) of
    Nothing -> Nothing
    Just (expr, s, _) ->
      Just (s, bimap (Subst.applyTySchema s) (Subst.applyTy s) expr)
