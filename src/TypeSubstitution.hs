module TypeSubstitution where

import qualified Data.List as List
import qualified Data.Maybe as Maybe

import Type(Type(..), TypeSchema(..))
import TypeContext(Context)

type Subst = [(String, Type)]

empty :: Subst
empty = []

add :: (String, Type) -> Subst -> Subst
add = (:)

singleton :: (String, Type) -> Subst
singleton p = add p empty

applyTy :: Subst -> Type -> Type
applyTy s (TFun t1 t2) = TFun (applyTy s t1) (applyTy s t2)
applyTy s (TVar x) = Maybe.fromMaybe (TVar x) (List.lookup x s)
applyTy s t = t

applyTySchema :: Subst -> TypeSchema -> TypeSchema
applyTySchema s (TSType ty) = TSType (applyTy s ty)
applyTySchema s (TSForall x ts) =
  let ts' = applyTySchema s ts in
  case List.lookup x s of
    Nothing -> TSForall x ts'
    Just _ -> ts'

applyContext :: Subst -> Context -> Context
applyContext s = map (\(x, tySchema) -> (x, applyTySchema s tySchema))

concat :: Subst -> Subst -> Subst
concat as bs = map (\(x, ty) -> (x, applyTy bs ty)) as ++ bs
