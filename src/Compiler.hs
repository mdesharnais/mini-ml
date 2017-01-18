{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module Compiler where

import qualified Data.List
import qualified Expr

import Data.List((\\))
import Expr(Expr(..), Id)
import FreshName
import Type(TyExpr, Type(..), TypeSchema(..))

-- Intermediate language in normal form

data AtomicExpr =
  ALitInt    Type Integer |
  ALitBool   Type Bool |
  AVar       Type Id |
  AExternVar Type Id

data ComplexExpr =
  COpAdd Type AtomicExpr AtomicExpr |
  COpSub Type AtomicExpr AtomicExpr |
  COpMul Type AtomicExpr AtomicExpr |
  COpDiv Type AtomicExpr AtomicExpr |
  COpLT  Type AtomicExpr AtomicExpr |
  COpEQ  Type AtomicExpr AtomicExpr |
  CIf    Type AtomicExpr ExprNF ExprNF |
  CApp   Type AtomicExpr AtomicExpr |
  CAbs   Type Id ExprNF

data ExprNF =
  EVal    Type AtomicExpr |
  ELet    Type Id ComplexExpr ExprNF |
  ELetRec Type (Id, TypeSchema) (Id, ExprNF) ExprNF

class Typeable a where
  getType :: a -> Type

instance Typeable AtomicExpr where
  getType (ALitInt    ty _) = ty
  getType (ALitBool   ty _) = ty
  getType (AVar       ty _) = ty
  getType (AExternVar ty _) = ty

instance Typeable ExprNF where
  getType (EVal    ty _) = ty
  getType (ELet    ty _ _ _) = ty
  getType (ELetRec ty _ _ _) = ty

-- Pretty print

instance Show AtomicExpr where
  show (ALitInt    _ n) = show n
  show (ALitBool   _ True) = "true"
  show (ALitBool   _ False) = "false"
  show (AVar       _ x) = x
  show (AExternVar _ f) = f

instance Show ComplexExpr where
  show (COpAdd _ e1 e2) = show e1 ++ " + " ++ show e2
  show (COpSub _ e1 e2) = show e1 ++ " - " ++ show e2
  show (COpMul _ e1 e2) = show e1 ++ " * " ++ show e2
  show (COpDiv _ e1 e2) = show e1 ++ " / " ++ show e2
  show (COpLT  _ e1 e2) = show e1 ++ " < " ++ show e2
  show (COpEQ  _ e1 e2) = show e1 ++ " = " ++ show e2
  show (CIf    _ e1 e2 e3) =
    "if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3
  show (CApp   _ e1 e2) = show e1 ++ " " ++ show e2
  show (CAbs   _ x e) = "(fun " ++ x ++ " -> " ++ show e ++ ")"

instance Show ExprNF where
  show (EVal    _ x) = show x
  show (ELet    _ x e1 e2) =
    "let " ++ x ++ " = " ++ show e1 ++ " in\n" ++ show e2
  show (ELetRec _ (x, _) (y, e1) e2) =
    "let rec " ++ x ++ " = (fun " ++ y ++ " -> " ++ show e1 ++ ") in\n" ++ show e2

-- Expression -> normal form

nfBinOp :: TyExpr -> TyExpr -> (Type -> AtomicExpr -> AtomicExpr -> ComplexExpr) ->
  Type -> (Type -> Id -> AtomicExpr) -> (AtomicExpr -> NameGen ExprNF) ->
  NameGen ExprNF
nfBinOp e1 e2 op ty s k = nf e1 s (\a -> nf e2 s (\b -> do
  c <- fresh
  d <- k (AVar ty c)
  return (ELet (getType d) c (op ty a b) d)))

nf :: TyExpr -> (Type -> Id -> AtomicExpr) -> (AtomicExpr -> NameGen ExprNF) ->
  NameGen ExprNF
nf (LitInt    ty n) s k = k (ALitInt ty n)
nf (LitBool   ty b) s k = k (ALitBool ty b)
nf (Var       ty x) s k = k (s ty x)
nf (ExternVar ty x) s k = k (AExternVar ty x)
nf (OpAdd     ty e1 e2) s k = nfBinOp e1 e2 COpAdd ty s k
nf (OpSub     ty e1 e2) s k = nfBinOp e1 e2 COpSub ty s k
nf (OpMul     ty e1 e2) s k = nfBinOp e1 e2 COpMul ty s k
nf (OpDiv     ty e1 e2) s k = nfBinOp e1 e2 COpDiv ty s k
nf (OpLT      ty e1 e2) s k = nfBinOp e1 e2 COpLT  ty s k
nf (OpEQ      ty e1 e2) s k = nfBinOp e1 e2 COpEQ  ty s k
nf (If        ty e1 e2 e3) s k = nf e1 s (\e1' -> do
  a <- fresh
  e2' <- nf e2 s (return . EVal (Expr.getType e2))
  e3' <- nf e3 s (return . EVal (Expr.getType e3))
  b <- k (AVar (Expr.getType e1) a)
  let ifTy = getType e2'
  return (ELet (getType b) a (CIf ifTy e1' e2' e3') b))
nf (Let ty (x, _) e1 e2) s k =
  nf e1 s (\a ->
  nf e2 (\ty y -> if y == x then a else s ty y) (return . EVal (Expr.getType e2)))
nf (LetRec ty (f, fTy) (x, e1) e2) s k = do
  let rmTySch (TSType ty) = ty
      rmTySch (TSForall _ ty) = rmTySch ty
  a <- fresh
  let subst ty y = if y == f then AVar ty a else s ty y
  e1' <- nf e1 subst (return . EVal (Expr.getType e1))
  e2' <- nf e2 subst (return . EVal (Expr.getType e2))
  return (ELetRec ty (a, fTy) (x, e1') e2')
nf (Abs ty x e) s k = do
  a <- fresh
  b <- nf e s (return . EVal (Expr.getType e))
  c <- k (AVar ty a)
  return (ELet (getType c) a (CAbs ty x b) c)
nf (App ty e1 e2) s k = nf e1 s (\e1' -> nf e2 s (\e2' -> do
  a <- fresh
  d <- k (AVar ty a)
  return (ELet (getType d) a (CApp ty e1' e2') d)))

toNormalFormM :: TyExpr -> NameGen ExprNF
toNormalFormM e = nf e AVar (return . EVal (Expr.getType e))

toNormalForm :: TyExpr -> ExprNF
toNormalForm = runNameGen . toNormalFormM

-- Intermediate language in normal form with closures

data AtomicExprCl =
  ACLitInt    Type Integer |
  ACLitBool   Type Bool |
  ACExternVar Type Id |
  ACVar       Type Id |
  ACVarSelf   Type |
  ACVarEnv    Type Integer

type Env = [AtomicExprCl]

data ComplexExprCl =
  CCOpAdd   Type AtomicExprCl AtomicExprCl |
  CCOpSub   Type AtomicExprCl AtomicExprCl |
  CCOpMul   Type AtomicExprCl AtomicExprCl |
  CCOpDiv   Type AtomicExprCl AtomicExprCl |
  CCOpLT    Type AtomicExprCl AtomicExprCl |
  CCOpEQ    Type AtomicExprCl AtomicExprCl |
  CCIf      Type AtomicExprCl ExprNFCl ExprNFCl |
  CCApp     Type AtomicExprCl AtomicExprCl |
  CCClosure Type Id ExprNFCl Env

data ExprNFCl =
  ECVal Type AtomicExprCl |
  ECLet Type Id ComplexExprCl ExprNFCl

-- Pretty print

instance Show AtomicExprCl where
  show (ACLitInt    _ n) = show n
  show (ACLitBool   _ b) = show b
  show (ACExternVar _ f) = show f
  show (ACVar       _ x) = x
  show (ACVarSelf   _)   = "env.self"
  show (ACVarEnv    _ n) = "env." ++ show n

instance Show ComplexExprCl where
  show (CCOpAdd   _ e1 e2) = show e1 ++ " + " ++ show e2
  show (CCOpSub   _ e1 e2) = show e1 ++ " - " ++ show e2
  show (CCOpMul   _ e1 e2) = show e1 ++ " * " ++ show e2
  show (CCOpDiv   _ e1 e2) = show e1 ++ " / " ++ show e2
  show (CCOpLT    _ e1 e2) = show e1 ++ " < " ++ show e2
  show (CCOpEQ    _ e1 e2) = show e1 ++ " = " ++ show e2
  show (CCIf      _ e1 e2 e3) =
    "if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3
  show (CCApp     _ e1 e2) = show e1 ++ " " ++ show e2
  show (CCClosure _ x f env) =
    "Closure (fun env -> fun " ++ x ++ " -> " ++ show f ++ ", " ++ show env ++ ")"

instance Show ExprNFCl where
  show (ECVal _ x) = show x
  show (ECLet _ x e1 e2) =
    "let " ++ x ++ " = " ++ show e1 ++ " in\n" ++ show e2

-- Normal form -> normal form with closure

class FreeVariables a where
  fv :: a -> [(Id, Type)]

instance FreeVariables AtomicExpr where
  fv (ALitInt    _ _) = []
  fv (ALitBool   _ _) = []
  fv (AVar       ty x) = [(x, ty)]
  fv (AExternVar _ x) = []

instance FreeVariables ComplexExpr where
  fv (COpAdd _ e1 e2) = Data.List.union (fv e1) (fv e2)
  fv (COpSub _ e1 e2) = Data.List.union (fv e1) (fv e2)
  fv (COpMul _ e1 e2) = Data.List.union (fv e1) (fv e2)
  fv (COpDiv _ e1 e2) = Data.List.union (fv e1) (fv e2)
  fv (COpLT  _ e1 e2) = Data.List.union (fv e1) (fv e2)
  fv (COpEQ  _ e1 e2) = Data.List.union (fv e1) (fv e2)
  fv (CIf    _ e1 e2 e3) =
    let u = Data.List.union in (fv e1) `u` (fv e2) `u` (fv e3)
  fv (CApp   _ e1 e2) = Data.List.union (fv e1) (fv e2)
  fv (CAbs   _ x e) = [p | p@(y,_) <- fv e, y /= x]

instance FreeVariables ExprNF where
  fv (EVal    _ x) = fv x
  fv (ELet    _ x e1 e2) = Data.List.union (fv e1) [p | p <- fv e2, fst p /= x]
  fv (ELetRec _ (f, _) (x, e1) e2) =
    Data.List.union
      [p | p@(y,_) <- fv e1, y /= f && y /= f]
      [p | p@(y,_) <- fv e2, y /= f]

clAt :: (Type -> Id -> AtomicExprCl) -> AtomicExpr -> AtomicExprCl
clAt s (ALitInt    ty n) = ACLitInt    ty n
clAt s (ALitBool   ty b) = ACLitBool   ty b
clAt s (AVar       ty  x) = s ty x
clAt s (AExternVar ty x) = ACExternVar ty x

clAbs ty s f (x, e) =
  let fvs = [p | p@(y,_) <- fv e, y /= f && y /= x] in
  let subst ty y =
        if x == y then
          ACVar ty x
        else
          case Data.List.elemIndex y (map fst fvs) of
            Nothing -> s ty y
            Just n  -> ACVarEnv (snd (fvs !! n)) (toInteger n)
   in CCClosure ty x (clExpr subst e) (map (uncurry (flip ACVar)) fvs)

clCo :: (Type -> Id -> AtomicExprCl) -> ComplexExpr -> ComplexExprCl
clCo s (COpAdd ty e1 e2)    = CCOpAdd ty (clAt s e1) (clAt s e2)
clCo s (COpSub ty e1 e2)    = CCOpSub ty (clAt s e1) (clAt s e2)
clCo s (COpMul ty e1 e2)    = CCOpMul ty (clAt s e1) (clAt s e2)
clCo s (COpDiv ty e1 e2)    = CCOpDiv ty (clAt s e1) (clAt s e2)
clCo s (COpLT  ty e1 e2)    = CCOpLT  ty (clAt s e1) (clAt s e2)
clCo s (COpEQ  ty e1 e2)    = CCOpEQ  ty (clAt s e1) (clAt s e2)
clCo s (CIf    ty e1 e2 e3) = CCIf    ty (clAt s e1) (clExpr s e2) (clExpr s e3)
clCo s (CApp   ty e1 e2)    = CCApp   ty (clAt s e1) (clAt s e2)
clCo s (CAbs   ty x e)      = clAbs ty s "" (x, e)

clExpr :: (Type -> Id -> AtomicExprCl) -> ExprNF -> ExprNFCl
clExpr s (EVal    ty a) = ECVal ty (clAt s a)
clExpr s (ELet    ty x e1 e2) = ECLet ty x (clCo s e1) (clExpr s e2)
clExpr s (ELetRec ty (f, fTy) (x, e1) e2) =
  let rmTySch (TSType ty) = ty
      rmTySch (TSForall _ tySch) = rmTySch tySch in
  ECLet ty f
    (clAbs (rmTySch fTy)
      (\ty g -> if g == f then ACVarSelf ty else s ty g) f (x, e1))
    (clExpr s e2)

toClosure :: ExprNF -> ExprNFCl
toClosure = clExpr ACVar
