{-# LANGUAGE DeriveFunctor #-}
module Type where

import qualified Data.List as List
import qualified Data.Set as Set

import Data.Set(Set)
import Expr(Expr(..))
import FreeVars

-- Data definitions

type TyVar = String

data BaseType a =
  TBool |
  TInt |
  TFun a (BaseType a) (BaseType a) |
  TVar TyVar
  deriving (Eq, Functor, Show)

type Type = BaseType AnVar

type AnVar = String

data Annotation = AFun | AClo deriving (Eq, Ord, Show)

type Type2 = BaseType (Set Annotation)

data BaseTypeSchema ty =
  TSType ty |
  TSForall TyVar (BaseTypeSchema ty)
  deriving (Eq, Functor, Show)

type TypeSchema = BaseTypeSchema Type
type TypeSchema2 = BaseTypeSchema Type2

type TyExpr = Expr TypeSchema Type
type TyExpr2 = Expr TypeSchema2 Type2

-- Type classes instances

{-
instance Show Type where
  show TBool = "bool"
  show TInt = "int"
  show (TFun b t1 t2) = "(" ++ show t1 ++ " ->{" ++ b ++ "} " ++ show t2 ++ ")"
  show (TVar x) = x
  -}

{-
instance Show TypeSchema where
  show (TSType t) = show t
  show (TSForall x t) = "forall " ++ x ++ ". " ++ show t
-}

instance FreeVars (BaseType a) where
  freeVars TBool = []
  freeVars TInt = []
  freeVars (TFun _ t1 t2) = List.union (freeVars t1) (freeVars t2)
  freeVars (TVar x) = [x]

instance FreeVars ty => FreeVars (BaseTypeSchema ty) where
  freeVars (TSType ty) = freeVars ty
  freeVars (TSForall x ty) = List.delete x (freeVars ty)

