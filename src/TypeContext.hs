module TypeContext where

import qualified Data.List as List

import FreeVars
import Type

type Context = [(TyVar, TypeSchema)]

add :: (TyVar, TypeSchema) -> Context -> Context
add = (:)

addTy :: (TyVar, Type) -> Context -> Context
addTy (x, ty) ctxt = (x, TSType ty) : ctxt

empty :: Context
empty = []

extractTypeVars :: Context -> [TyVar]
extractTypeVars =
  let extractTySchema (TSType ty) = freeVars ty
      extractTySchema (TSForall _ tySchema) = extractTySchema tySchema
   in List.concat . map (extractTySchema . snd)

fromListTy :: [(TyVar, Type)] -> Context
fromListTy = List.foldl (flip addTy) empty

lookup :: TyVar -> Context -> Maybe TypeSchema
lookup = List.lookup

singleton :: (TyVar, Type) -> Context
singleton p = addTy p empty
