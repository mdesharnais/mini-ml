module Expr where

import qualified Data.List as List

import Data.Bifunctor
import FreeVars

type Id = String

data Expr tySch ty =
  LitInt    ty Integer |
  LitBool   ty Bool |
  Var       ty Id |
  ExternVar ty Id |
  OpAdd     ty (Expr tySch ty) (Expr tySch ty) |
  OpSub     ty (Expr tySch ty) (Expr tySch ty) |
  OpMul     ty (Expr tySch ty) (Expr tySch ty) |
  OpDiv     ty (Expr tySch ty) (Expr tySch ty) |
  OpLT      ty (Expr tySch ty) (Expr tySch ty) |
  OpEQ      ty (Expr tySch ty) (Expr tySch ty) |
  If        ty (Expr tySch ty) (Expr tySch ty) (Expr tySch ty) |
  Let       ty (Id, tySch) (Expr tySch ty) (Expr tySch ty) |
  LetRec    ty (Id, tySch) (Id, (Expr tySch ty)) (Expr tySch ty) |
  Abs       ty Id (Expr tySch ty) |
  App       ty (Expr tySch ty) (Expr tySch ty)
  deriving (Eq, Show)

getType :: Expr sch ty -> ty
getType (LitInt    ty _) = ty
getType (LitBool   ty _) = ty
getType (Var       ty _) = ty
getType (ExternVar ty _) = ty
getType (OpAdd     ty _ _) = ty
getType (OpSub     ty _ _) = ty
getType (OpMul     ty _ _) = ty
getType (OpDiv     ty _ _) = ty
getType (OpLT      ty _ _) = ty
getType (OpEQ      ty _ _) = ty
getType (If        ty _ _ _) = ty
getType (Let       ty _ _ _) = ty
getType (LetRec    ty _ _ _) = ty
getType (Abs       ty _ _) = ty
getType (App       ty _ _) = ty

instance Bifunctor Expr where
  bimap f g (LitInt    ty n) = LitInt    (g ty) n
  bimap f g (LitBool   ty b) = LitBool   (g ty) b
  bimap f g (Var       ty x) = Var       (g ty) x
  bimap f g (ExternVar ty x) = ExternVar (g ty) x
  bimap f g (OpAdd     ty e1 e2) = OpAdd (g ty) (bimap f g e1) (bimap f g e2)
  bimap f g (OpSub     ty e1 e2) = OpSub (g ty) (bimap f g e1) (bimap f g e2)
  bimap f g (OpMul     ty e1 e2) = OpMul (g ty) (bimap f g e1) (bimap f g e2)
  bimap f g (OpDiv     ty e1 e2) = OpDiv (g ty) (bimap f g e1) (bimap f g e2)
  bimap f g (OpLT      ty e1 e2) = OpLT  (g ty) (bimap f g e1) (bimap f g e2)
  bimap f g (OpEQ      ty e1 e2) = OpEQ  (g ty) (bimap f g e1) (bimap f g e2)
  bimap f g (If        ty e e1 e2) =
    If (g ty) (bimap f g e) (bimap f g e1) (bimap f g e2)
  bimap f g (Let       ty (x, xTy) e1 e2) =
    Let (g ty) (x, f xTy) (bimap f g e1) (bimap f g e2)
  bimap f g (LetRec    ty (y, yTy) (x, e1) e2) =
    LetRec (g ty) (y, f yTy) (x, (bimap f g e1)) (bimap f g e2)
  bimap f g (Abs       ty x e) = Abs (g ty) x (bimap f g e)
  bimap f g (App       ty e1 e2) = App (g ty) (bimap f g e1) (bimap f g e2)

{-
instance (Show tySch, Show ty) => Show (Expr tySch ty) where
  show (LitInt _ n) = show n
  show (LitBool _ b) = show b
  show (Var ty x) = "(" ++ x ++ " : " ++ show ty ++ ")"
  show (ExternVar _ x) = x
  show (OpAdd _ e1 e2) = "(" ++ show e1 ++ " + " ++ show e2 ++ ")"
  show (OpSub _ e1 e2) = "(" ++ show e1 ++ " - " ++ show e2 ++ ")"
  show (OpMul _ e1 e2) = "(" ++ show e1 ++ " * " ++ show e2 ++ ")"
  show (OpDiv _ e1 e2) = "(" ++ show e1 ++ " / " ++ show e2 ++ ")"
  show (OpLT  _ e1 e2) = "(" ++ show e1 ++ " < " ++ show e2 ++ ")"
  show (OpEQ  _ e1 e2) = "(" ++ show e1 ++ " = " ++ show e2 ++ ")"
  show (If _ e1 e2 e3) =
    "if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3
  show (Let _ (x, ty) e1 e2) =
    "let " ++ x ++ " : " ++ show ty ++ " = " ++
    show e1 ++ " in " ++ show e2
  show (LetRec _ (f, ty) (x, e1) e2) =
    "let rec " ++ f ++ " : " ++ show ty ++ " = " ++
    "fun " ++ x ++ " -> " ++ show e1 ++ " in " ++ show e2
  show (Abs _ x e1) = "(fun " ++ x ++ " -> " ++ show e1 ++ ")"
  show (App ty e1 e2) =
    "(" ++ show e1 ++ " " ++ show e2 ++ " : " ++ show ty ++ ")"
-}

instance FreeVars (Expr a b) where
  freeVars (LitInt _ n)         = []
  freeVars (LitBool _ b)        = []
  freeVars (Var ty x)           = [x]
  freeVars (ExternVar _ x)      = [x]
  freeVars (OpAdd _ e1 e2)      = List.union (freeVars e1) (freeVars e2)
  freeVars (OpSub _ e1 e2)      = List.union (freeVars e1) (freeVars e2)
  freeVars (OpMul _ e1 e2)      = List.union (freeVars e1) (freeVars e2)
  freeVars (OpDiv _ e1 e2)      = List.union (freeVars e1) (freeVars e2)
  freeVars (OpLT  _ e1 e2)      = List.union (freeVars e1) (freeVars e2)
  freeVars (OpEQ  _ e1 e2)      = List.union (freeVars e1) (freeVars e2)
  freeVars (If _ e1 e2 e3)      =
    let u = List.union in (freeVars e1) `u` (freeVars e2) `u` (freeVars e2)
  freeVars (Let _ (x, _) e1 e2) =
    List.union (freeVars e1) [a | a <- freeVars e2, a /= x]
  freeVars (LetRec _ (f, _) (x, e1) e2) =
    List.union
      [a | a <- freeVars e1, a /= f && a /= x]
      [a | a <- freeVars e2, a /= f]
  freeVars (Abs _ x e1)         = [a | a <- freeVars e1, a /= x]
  freeVars (App ty e1 e2)       = List.union (freeVars e1) (freeVars e2)
