module TypeContext where

import qualified Data.List as List

import Type(Type(..), TypeSchema(..), freeVars)

type Context = [(String, TypeSchema)]

add :: (String, TypeSchema) -> Context -> Context
add = (:)

addTy :: (String, Type) -> Context -> Context
addTy (x, ty) ctxt = (x, TSType ty) : ctxt

empty :: Context
empty = []


extractTypeVars :: Context -> [String]
extractTypeVars =
  let extractTySchema (TSType ty) = freeVars ty
      extractTySchema (TSForall _ tySchema) = extractTySchema tySchema
   in List.concat . map (extractTySchema . snd)

fromListTy :: [(String, Type)] -> Context
fromListTy = List.foldl (flip addTy) empty

lookup :: String -> Context -> Maybe TypeSchema
lookup = List.lookup

singleton :: (String, Type) -> Context
singleton p = addTy p empty
