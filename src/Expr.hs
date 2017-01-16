module Expr where

type Id = String

data Expr ty =
  LitInt    ty Integer |
  LitBool   ty Bool |
  Var       ty Id |
  ExternVar ty Id |
  OpAdd     ty (Expr ty) (Expr ty) |
  OpSub     ty (Expr ty) (Expr ty) |
  OpMul     ty (Expr ty) (Expr ty) |
  OpDiv     ty (Expr ty) (Expr ty) |
  OpLT      ty (Expr ty) (Expr ty) |
  OpEQ      ty (Expr ty) (Expr ty) |
  If        ty (Expr ty) (Expr ty) (Expr ty) |
  Let       ty Id (Expr ty) (Expr ty) |
  LetRec    ty Id (ty, Id, (Expr ty)) (Expr ty) |
  Abs       ty Id (Expr ty) |
  App       ty (Expr ty) (Expr ty)
  deriving (Eq)

getType :: Expr ty -> ty
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

instance Show ty => Show (Expr ty) where
  show (LitInt _ n) = show n
  show (LitBool _ b) = show b
  show (Var _ x) = x
  show (ExternVar _ x) = x
  show (OpAdd _ e1 e2) = "(" ++ show e1 ++ " + " ++ show e2 ++ ")"
  show (OpSub _ e1 e2) = "(" ++ show e1 ++ " - " ++ show e2 ++ ")"
  show (OpMul _ e1 e2) = "(" ++ show e1 ++ " * " ++ show e2 ++ ")"
  show (OpDiv _ e1 e2) = "(" ++ show e1 ++ " / " ++ show e2 ++ ")"
  show (OpLT  _ e1 e2) = "(" ++ show e1 ++ " < " ++ show e2 ++ ")"
  show (OpEQ  _ e1 e2) = "(" ++ show e1 ++ " = " ++ show e2 ++ ")"
  show (If _ e1 e2 e3) =
    "if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3
  show (Let _ x e1 e2) =
    "let " ++ x ++ " = " ++ show e1 ++ " in " ++ show e2
  show (LetRec _ f (ty, x, e1) e2) =
    "let rec " ++ f ++ " : " ++ show ty ++ " = " ++
    "fun " ++ x ++ " -> " ++ show e1 ++ " in " ++ show e2
  show (Abs _ x e1) = "(fun " ++ x ++ " -> " ++ show e1 ++ ")"
  show (App _ e1 e2) = show e1 ++ " " ++ show e2
