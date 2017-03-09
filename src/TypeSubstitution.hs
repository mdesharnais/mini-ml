module TypeSubstitution where

import qualified Data.List as List
import qualified Data.Maybe as Maybe

import Type
import TypeContext(Context)

type TySubst = [(TyVar, Type)]
type AnSubst = [(AnVar, AnVar)]
type Subst = (TySubst, AnSubst)

empty :: Subst
empty = ([], [])

addTy :: (TyVar, Type) -> Subst -> Subst
addTy p (ts, as) = (p : ts, as)

addAn :: (AnVar, AnVar) -> Subst -> Subst
addAn p (ts, as) = (ts, p : as)

singletonTy :: (TyVar, Type) -> Subst
singletonTy p = addTy p empty

singletonAn :: (AnVar, AnVar) -> Subst
singletonAn p = addAn p empty

applyAn :: Subst -> AnVar -> AnVar
applyAn (_, as) a = Maybe.fromMaybe a (List.lookup a as)

applyTy :: Subst -> Type -> Type
applyTy s@(ts, as) TBool = TBool
applyTy s@(ts, as) TInt = TInt
applyTy s@(ts, as) (TFun b t1 t2) =
  TFun (applyAn s b) (applyTy s t1) (applyTy s t2)
applyTy s@(ts, as) (TVar x) = Maybe.fromMaybe (TVar x) (List.lookup x ts)

applyTySchema :: Subst -> TypeSchema -> TypeSchema
applyTySchema s (TSType ty) = TSType (applyTy s ty)
applyTySchema s@(xs, _) (TSForall x ts) =
  let ts' = applyTySchema s ts in
  case List.lookup x xs of
    Nothing -> TSForall x ts'
    Just ty ->
      case ty of
        TBool -> ts'
        TInt -> ts'
        (TFun _ _ _) -> ts'
        (TVar y) -> if x == y then TSForall x ts' else ts'

applyContext :: Subst -> Context -> Context
applyContext s = map (\(x, tySchema) -> (x, applyTySchema s tySchema))

comp :: Subst -> Subst -> Subst
comp (as, bs) (cs, ds) =
  let compLists xs ys apply = map (\(x, y) -> (x, apply ys y)) xs ++ ys in
  let ts = compLists cs as (applyTy . flip (,) []) in
  let as = compLists ds bs (applyAn . (,) []) in
  (ts, as)
