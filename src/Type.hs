module Type where

import qualified Control.Monad
import qualified Data.List as List
import qualified Data.Maybe
import qualified Expr

import Control.Monad.Trans(lift)
import Data.Bifunctor(bimap)
import Data.List((\\))
import Expr(Expr(..))
import FreshName

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

type Context = [(String, TypeSchema)]

emptyContext :: Context
emptyContext = []

addContext :: (String, Type) -> Context -> Context
addContext (x, ty) ctxt = (x, TSType ty) : ctxt

addTySchemaToContext :: (String, TypeSchema) -> Context -> Context
addTySchemaToContext = (:)

lookupContext :: String -> Context -> Maybe TypeSchema
lookupContext = List.lookup

singletonContext :: (String, Type) -> Context
singletonContext p = addContext p emptyContext

contextFromList :: [(String, Type)] -> Context
contextFromList = List.foldl (flip addContext) emptyContext

extractTypeVars :: Context -> [String]
extractTypeVars =
  let extractFromTySchema (TSType ty) = freeVars ty
      extractFromTySchema (TSForall _ tySchema) = extractFromTySchema tySchema
   in List.concat . map (extractFromTySchema . snd)

type Subst = [(String, Type)]

emptySubst :: Subst
emptySubst = []

addSubst :: (String, Type) -> Subst -> Subst
addSubst = (:)

singletonSubst :: (String, Type) -> Subst
singletonSubst p = addSubst p emptySubst

applyOnType :: Subst -> Type -> Type
applyOnType s (TFun t1 t2) = TFun (applyOnType s t1) (applyOnType s t2)
applyOnType s (TVar x) = Data.Maybe.fromMaybe (TVar x) (List.lookup x s)
applyOnType s t = t

applyOnTypeSchema :: Subst -> TypeSchema -> TypeSchema
applyOnTypeSchema s (TSType ty) = TSType (applyOnType s ty)
applyOnTypeSchema s (TSForall x ts) =
  let ts' = applyOnTypeSchema s ts in
  case List.lookup x s of
    Nothing -> TSForall x ts'
    Just _ -> ts'

applyOnContext :: Subst -> Context -> Context
applyOnContext s = map (\(x, tySchema) -> (x, applyOnTypeSchema s tySchema))

concatSubst :: Subst -> Subst -> Subst
concatSubst as bs = map (\(x, ty) -> (x, applyOnType bs ty)) as ++ bs

genFreshTVar :: Monad m => NameGenT m Type
genFreshTVar = fresh >>= (return . TVar)

unify :: Type -> Type -> Maybe Subst
unify (TVar x) (TVar y) = Just $
  if x == y then emptySubst else singletonSubst (x, TVar y)
unify (TVar x) t =
  if List.elem x (freeVars t) then Nothing else Just (singletonSubst (x, t))
unify t (TVar x) =
  if List.elem x (freeVars t) then Nothing else Just (singletonSubst (x, t))
unify (TFun t1 t2) (TFun t1' t2') = do
  s1 <- unify t1 t1'
  s2 <- unify (applyOnType s1 t2) (applyOnType s1 t2')
  Just (concatSubst s1 s2)
unify x y = if x == y then Just emptySubst else Nothing

infer :: Context -> Expr () () -> Maybe (Subst, TyExpr)
infer c e = do
  case runNameGenTWithout (extractTypeVars c) (impl c e) of
    Nothing -> Nothing
    Just (s, expr) ->
      Just (s, bimap (applyOnTypeSchema s) (applyOnType s) expr)
  where cat = concatSubst
        app = applyOnContext

        checkBinOpElements
          :: (Type -> TyExpr -> TyExpr -> TyExpr)  -- ^ The constructor
          -> Type       -- ^ The type of the left hand side
          -> Type       -- ^ The type of the right hand side
          -> Type       -- ^ The type of the resulting expression
          -> Context    -- ^ Context in which the expressions are type-checked
          -> Expr () () -- ^ Left hand side expression
          -> Expr () () -- ^ Right hand side expression
          -> NameGenT Maybe (Subst, TyExpr)
        checkBinOpElements con t1 t2 t c e1 e2 = do
          (s1, e1') <- impl c e1
          s1' <- lift (unify (Expr.getType e1') t1)
          let s1'' = s1 `cat` s1'
          (s2, e2') <- impl (s1'' `app` c) e2
          s2' <- lift (unify (Expr.getType e2') t2)
          return (s1'' `cat` s2 `cat` s2', con t e1' e2')

        impl :: Context -> Expr () () -> NameGenT Maybe (Subst, TyExpr)
        impl c (Var _ x) = do
          let instanciate :: Monad m => Subst -> TypeSchema -> NameGenT m Type
              instanciate s (TSType ty) = return (applyOnType s ty)
              instanciate s (TSForall x tySchema) = do
                alpha <- genFreshTVar
                instanciate (addSubst (x, alpha) s) tySchema
          tySchema <- lift (lookupContext x c)
          alpha <- instanciate emptySubst tySchema
          return (emptySubst, Var alpha x)
        impl c (ExternVar _ x) = do
          return (emptySubst, ExternVar (TFun TInt TInt) x)
        impl c (Abs _ x e) = do
          alpha <- genFreshTVar
          (s, e') <- impl (addContext (x, alpha) c) e
          let tau = TFun (applyOnType s alpha) (Expr.getType e')
          return (s, Abs tau x e')
        impl c (App _ e1 e2) = do
          (s1, e1') <- impl c e1
          (s2, e2') <- impl (s1 `app` c) e2
          beta <- genFreshTVar
          s3 <- lift $ unify
            (applyOnType s2 (Expr.getType e1')) (TFun (Expr.getType e2') beta)
          return (s1 `cat` s2 `cat` s3,
            App (applyOnType s3 beta) e1' e2')
        impl c (LitInt  _ n) = return (emptySubst, LitInt TInt n)
        impl c (LitBool _ b) = return (emptySubst, LitBool TBool b)
        impl c (OpMul _ e1 e2) = checkBinOpElements OpMul TInt TInt TInt  c e1 e2
        impl c (OpDiv _ e1 e2) = checkBinOpElements OpDiv TInt TInt TInt  c e1 e2
        impl c (OpAdd _ e1 e2) = checkBinOpElements OpAdd TInt TInt TInt  c e1 e2
        impl c (OpSub _ e1 e2) = checkBinOpElements OpSub TInt TInt TInt  c e1 e2
        impl c (OpLT  _ e1 e2) = checkBinOpElements OpLT  TInt TInt TBool c e1 e2
        impl c (OpEQ  _ e1 e2) = checkBinOpElements OpEQ  TInt TInt TBool c e1 e2
        impl c (If _ e e1 e2) = do
          (s1, e') <- impl c e
          s2 <- lift $ unify (Expr.getType e') TBool
          let s3 = s1 `cat` s2
          (theta1, e1') <- impl (s3 `app` c) e1
          (theta2, e2') <- impl ((theta1 `cat` s3) `app` c) e2
          let tau2 = Expr.getType e2'
          theta3 <- lift $ unify (applyOnType theta2 (Expr.getType e1')) tau2
          return (s3 `cat` theta1 `cat` theta2 `cat` theta3,
            If (applyOnType theta3 tau2) e' e1' e2')
        impl c (Let _ (x, _) e1 e2) = do
          (theta1, e1') <- impl c e1
          let theta1' = theta1 `app` c
          let tau1 = Expr.getType e1'
          let fv = freeVars tau1
          let tyVars = fv \\ (extractTypeVars theta1')
          let tau1' = List.foldl (flip TSForall) (TSType tau1) tyVars
          (theta2, e2') <- impl (addTySchemaToContext (x, tau1') theta1') e2
          return (theta1 `cat` theta2, Let (Expr.getType e2') (x, tau1') e1' e2')
        impl c (LetRec _ (f, _) (y, e1) e2) = do
          alpha <- genFreshTVar
          (theta1, a@(Abs tau1 _ e1')) <-
            impl (addContext (f, alpha) c) (Abs () y e1)
          s <- lift (unify (applyOnType theta1 alpha) tau1)
          let theta1' = theta1 `app` c
          let fv = freeVars tau1
          let tyVars = fv \\ (extractTypeVars (s `app` theta1'))
          let tau1' = List.foldl (flip TSForall) (TSType tau1) tyVars
          (theta2, e2') <- impl (s `app` (addTySchemaToContext (f, tau1') theta1')) e2
          return (theta1 `cat` s `cat` theta2, LetRec (Expr.getType e2') (f, tau1') (y, e1') e2')
