module Type where

import qualified Data.List as List

import Expr(Expr(..))
import FreeVars

-- Data definitions

type TyVar = String

type AnVar = String

data Type =
  TBool |
  TInt |
  TFun AnVar Type Type |
  TVar TyVar
  deriving (Eq, Show)

data TypeSchema =
  TSType Type |
  TSForall TyVar TypeSchema
  deriving (Eq, Show)

type TyExpr = Expr TypeSchema Type

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

instance FreeVars Type where
  freeVars TBool = []
  freeVars TInt = []
  freeVars (TFun _ t1 t2) = List.union (freeVars t1) (freeVars t2)
  freeVars (TVar x) = [x]

instance FreeVars TypeSchema where
  freeVars (TSType ty) = freeVars ty
  freeVars (TSForall x ty) = List.delete x (freeVars ty)

