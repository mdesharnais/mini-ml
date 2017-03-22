module TypeInference where

import qualified Control.Monad
import qualified Data.List as List
import qualified Data.Maybe
import qualified Data.Set as Set
import qualified Expr
import qualified TypeContext as Context
import qualified TypeSubstitution as Subst

import Control.Monad.Trans(lift)
import Data.Bifunctor(bimap)
import Data.List((\\))
import Data.Set(Set)
import Expr(Expr(..))
import FreeVars
import FreshName
import Type
import TypeContext(Context)
import TypeSubstitution(Subst)

import Debug.Trace(traceShowId)

data SAnn = SASingleton Annotation | SAUnion SAnn SAnn | SAEmpty | SAVar AnVar
  deriving (Eq, Ord)

type Constraint = (AnVar, Annotation)

substApplyConstraint :: Subst -> Constraint -> Constraint
substApplyConstraint s (x, ann) = (Subst.applyAn s x, ann)

substApplyConstraints :: Subst -> Set Constraint -> Set Constraint
substApplyConstraints = Set.map . substApplyConstraint

genFreshTVar :: Monad m => NameGenT m Type
genFreshTVar = fmap TVar fresh

freshAVar :: Monad m => NameGenT m AnVar
freshAVar = fresh

occursIn x ty =
  case ty of
    TInt -> False
    TBool -> False
    (TFun _ t1 t2) -> occursIn x t1 || occursIn x t2
    (TVar y) -> x == y


unify :: Type -> Type -> Either String Subst
unify TInt TInt = return Subst.empty
unify TBool TBool = return Subst.empty
unify (TFun b t1 t2) (TFun b' t1' t2') = do
  let app = Subst.applyTy
  let o = Subst.comp
  s0 <- return (Subst.singletonAn (b', b))
  s1 <- unify (app s0 t1) (app s0 t1')
  s2 <- unify (app s1 (app s0 t2)) (app s1 (app s0 t2'))
  return (s2 `o` s1 `o` s0)
unify t alpha@(TVar x) =
  if t == alpha then
    return Subst.empty
  else if not (occursIn x t) then
    return (Subst.singletonTy (x, t))
  else
    Left ("Cannot unify '" ++ show t ++ "' and '" ++ show alpha ++ "'")
unify alpha@(TVar x) t = unify t alpha
{-
unify (TVar x) (TVar y) = Just $
  if x == y then Subst.empty else Subst.singletonTy (x, TVar y)
unify (TVar x) t =
  if List.elem x (freeVars t) then Nothing else Just (Subst.singletonTy (x, t))
unify t (TVar x) =
  if List.elem x (freeVars t) then Nothing else Just (Subst.singletonTy (x, t))
-}
unify t1 t2 =
    Left ("Cannot unify '" ++ show t1 ++ "' and '" ++ show t2 ++ "'")

infer :: Context -> Expr () () -> Either String (Subst, Set Constraint, TyExpr)
infer c e = do
  case runNameGenTWithout (Context.extractTypeVars c) (impl c e) of
    Left msg -> Left msg
    Right (s, cs, expr) ->
      Right (s, cs, bimap (Subst.applyTySchema s) (Subst.applyTy s) expr)
  where cat = Subst.comp
        o = Subst.comp

        checkBinOpElements
          :: (Type -> TyExpr -> TyExpr -> TyExpr)  -- ^ The constructor
          -> Type       -- ^ The type of the left hand side
          -> Type       -- ^ The type of the right hand side
          -> Type       -- ^ The type of the resulting expression
          -> Context    -- ^ Context in which the expressions are type-checked
          -> Expr () () -- ^ Left hand side expression
          -> Expr () () -- ^ Right hand side expression
          -> NameGenT (Either String) (Subst, Set Constraint, TyExpr)
        checkBinOpElements con t1 t2 t c e1 e2 = do
          (s1, cs1, e1') <- impl c e1
          (s2, cs2, e2') <- impl (Subst.applyContext s1 c) e2
          s3 <- lift (unify (Subst.applyTy s2 (Expr.getType e1')) t1)
          s4 <- lift (unify (Subst.applyTy s3 (Expr.getType e2')) t2)
          let app = substApplyConstraints
          let cs = Set.union
                (app s4 (app s3 (app s2 (app s1 cs1))))
                (app s4 (app s3 cs2))
          return (s4 `o` s3 `o` s2 `o` s1, cs, con t e1' e2')

        impl :: Context -> Expr () () ->
          NameGenT (Either String) (Subst, Set Constraint, TyExpr)
        impl c (Var _ x) = do
          let instanciate :: Monad m => Subst -> TypeSchema -> NameGenT m Type
              instanciate s (TSType ty) = return (Subst.applyTy s ty)
              instanciate s (TSForall x tySchema) = do
                alpha <- genFreshTVar
                instanciate (Subst.addTy (x, alpha) s) tySchema
          tySchema <- lift $
            case Context.lookup x c of
              Nothing -> Left ("Variable '" ++ x ++ "' not in context")
              Just tySchema -> Right tySchema
          alpha <- instanciate Subst.empty tySchema
          return (Subst.empty, Set.empty, Var alpha x)
        impl c (ExternVar _ x) = do
          beta <- freshAVar
          let cs = Set.singleton (beta, AFun)
          let ty = TFun beta TInt TInt
          return (Subst.empty, cs, ExternVar ty x)
        impl c (Abs _ x e1) = do
          alpha <- genFreshTVar
          (s1, cs1, e1') <- impl (Context.addTy (x, alpha) c) e1
          beta <- freshAVar
          let pi = if List.null (freeVars e1 \\ [x]) then AFun else AClo
          let cs = Set.insert (beta, pi) cs1
          let tau = TFun beta (Subst.applyTy s1 alpha) (Expr.getType e1')
          return (s1, cs, Abs tau x e1')
        impl c (AbsRec _ f x e1) = do
          let appTy = Subst.applyTy
          let appAn = Subst.applyAn
          let app = substApplyConstraints
          alphaX <- genFreshTVar
          alpha <- genFreshTVar
          beta <- freshAVar
          let fTy = TFun beta alphaX alpha
          let c' = Context.addTy (x, alphaX) (Context.addTy (f, fTy) c)
          (s1, cs1, e1') <- impl c' e1
          let e1Ty = Expr.getType e1'
          s2 <- lift $ unify e1Ty (appTy s1 alpha)
          let beta' = appAn s2 (appAn s1 beta)
          let ty = TFun beta' (appTy s2 (appTy s1 alphaX)) (appTy s2 e1Ty)
          let pi = if List.null (freeVars e1 \\ [f, x]) then AFun else AClo
          let cs = Set.insert (beta', pi) (app s2 (app s1 cs1))
          return (s2 `o` s1, cs, AbsRec ty f x e1')
        impl c (App _ e1 e2) = do
          (s1, cs1, e1') <- impl c e1
          (s2, cs2, e2') <- impl (Subst.applyContext s1 c) e2
          alpha <- genFreshTVar
          beta <- freshAVar
          s3 <- lift $ unify
            (Subst.applyTy s2 (Expr.getType e1'))
            (TFun beta (Expr.getType e2') alpha)
          let app = substApplyConstraints
          let cs = Set.union (app s3 (app s2 cs1)) (app s3 cs2)
          return (s3 `o` s2 `o` s1, cs, App (Subst.applyTy s3 alpha) e1' e2')
        impl c (LitInt  _ n) = return (Subst.empty, Set.empty, LitInt TInt n)
        impl c (LitBool _ b) = return (Subst.empty, Set.empty, LitBool TBool b)
        impl c (OpMul _ e1 e2) = checkBinOpElements OpMul TInt TInt TInt  c e1 e2
        impl c (OpDiv _ e1 e2) = checkBinOpElements OpDiv TInt TInt TInt  c e1 e2
        impl c (OpAdd _ e1 e2) = checkBinOpElements OpAdd TInt TInt TInt  c e1 e2
        impl c (OpSub _ e1 e2) = checkBinOpElements OpSub TInt TInt TInt  c e1 e2
        impl c (OpLT  _ e1 e2) = checkBinOpElements OpLT  TInt TInt TBool c e1 e2
        impl c (OpEQ  _ e1 e2) = checkBinOpElements OpEQ  TInt TInt TBool c e1 e2
        impl c (If _ e0 e1 e2) = do
          (s0, cs0, e0') <- impl c e0
          let c' = Subst.applyContext s0 c
          (s1, cs1, e1') <- impl c' e1
          let c'' = Subst.applyContext s1 c'
          (s2, cs2, e2') <- impl c'' e2
          let e0Ty = Expr.getType e0'
          let e1Ty = Expr.getType e1'
          let e2Ty = Expr.getType e2'
          let appTy = Subst.applyTy
          s3 <- lift $ unify (appTy s2 (appTy s1 e0Ty)) TBool
          s4 <- lift $ unify (appTy s2 e1Ty) e2Ty
          let ty = appTy s4 (appTy s3 e2Ty)
          let app = substApplyConstraints
          let cs0' = s4 `app` (s3 `app` (s2 `app` (s1 `app` cs0)))
          let cs1' = s4 `app` (s3 `app` (s2 `app` cs1))
          let cs2' = s4 `app` (s3 `app` cs2)
          let cs = cs0' `Set.union` cs1' `Set.union` cs2'
          return (s4 `o` s3 `o` s2 `o` s1 `o` s0, cs, If ty e0' e1' e2')
        impl c (Let _ (x, _) e1 e2) = do
          (s1, cs1, e1') <- impl c e1
          let e1Ty = Expr.getType e1'
          let c' = Subst.applyContext s1 c
          let tyVars = (freeVars e1Ty) \\ (Context.extractTypeVars c')
          let e1Ty' = List.foldl (flip TSForall) (TSType e1Ty) tyVars
          (s2, cs2, e2') <- impl (Context.add (x, e1Ty') c') e2
          let e2Ty = Expr.getType e2'
          let cs = Set.union (substApplyConstraints s2 cs1) cs2
          return (s2 `o` s1, cs, Let e2Ty (x, e1Ty') e1' e2')

infer2 :: Context -> Expr () () -> Either String TyExpr2
infer2 c expr = do
  (_, cs, expr') <- infer c expr
  let f :: Type -> Type2
      f = fmap (\a -> Set.map snd (Set.filter ((==) a . fst) cs))
  let g :: TypeSchema -> TypeSchema2
      g = fmap f
  return (bimap g f expr')
