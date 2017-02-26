module Type where

import qualified Data.List as List

import Expr(Expr(..))

-- Data definitions

data Type =
  TBool |
  TInt |
  TFun Type Type |
  TVar String
  deriving (Eq)

data TypeSchema =
  TSType Type |
  TSForall String TypeSchema
  deriving (Eq)

type TyExpr = Expr TypeSchema Type

-- Type classes instances

instance Show Type where
  show TBool = "bool"
  show TInt = "int"
  show (TFun t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (TVar x) = x

instance Show TypeSchema where
  show (TSType t) = show t
  show (TSForall x t) = "forall " ++ x ++ ". " ++ show t

class FreeVars a where
  freeVars :: a -> [String]

instance FreeVars Type where
  freeVars TBool = []
  freeVars TInt = []
  freeVars (TFun t1 t2) = List.union (freeVars t1) (freeVars t2)
  freeVars (TVar x) = [x]

instance FreeVars TypeSchema where
  freeVars (TSType ty) = freeVars ty
  freeVars (TSForall x ty) = List.delete x (freeVars ty)

