module TypeSubstitution where

import qualified Data.List as List
import qualified Data.Maybe as Maybe

import Data.Bifunctor(bimap)
import Expr
import Type
import TypeContext(Context)

type TySubst = Type -> Type
type AnSubst = AnVar -> AnVar
type Subst = (TySubst, AnSubst)

empty :: Subst
empty = (id, id)

addTy :: (TyVar, Type) -> Subst -> Subst
addTy (x, xTy) (ts, as) = (\y -> if TVar x == y then xTy else ts y, as)

addAn :: (AnVar, AnVar) -> Subst -> Subst
addAn (x, y) (ts, as) = (ts, \z -> if x == z then y else as z)

singletonTy :: (TyVar, Type) -> Subst
singletonTy p = addTy p empty

singletonAn :: (AnVar, AnVar) -> Subst
singletonAn p = addAn p empty

applyAn :: Subst -> AnVar -> AnVar
applyAn = snd

applyTy :: Subst -> Type -> Type
applyTy s@(ts, _) TBool = TBool
applyTy s@(ts, _) TInt = TInt
applyTy s@(ts, _) (TFun b t1 t2) =
  TFun (applyAn s b) (applyTy s t1) (applyTy s t2)
applyTy s@(ts, _) v@(TVar x) = ts v

applyTySchema :: Subst -> TypeSchema -> TypeSchema
applyTySchema s (TSType ty) = TSType (applyTy s ty)
applyTySchema s@(xs, _) (TSForall x ts) =
  let ts' = applyTySchema s ts in
  case applyTy s (TVar x) of
    TBool -> ts'
    TInt -> ts'
    (TFun _ _ _) -> ts'
    (TVar y) -> TSForall y ts'
    --(TVar y) -> if x == y then TSForall x ts' else ts'

applyContext :: Subst -> Context -> Context
applyContext s = map (\(x, tySchema) -> (x, applyTySchema s tySchema))

applyExpr :: Subst -> Expr TypeSchema Type -> Expr TypeSchema Type
applyExpr s = bimap (applyTySchema s) (applyTy s)

comp :: Subst -> Subst -> Subst
comp (as, bs) (cs, ds) = (as . cs, bs . ds)
