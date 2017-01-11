module Type where

import qualified Control.Monad
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import qualified Expr

import Control.Monad.Trans(lift)
import Data.List((\\))
import Expr(Expr, TyExpr(..))
import FreshName

data Type =
  TBool |
  TInt |
  TClosure Type Type |
  TFun Type Type |
  TVar String
  deriving (Eq)

data TypeSchema =
  TSType Type |
  TSForall String TypeSchema

instance Show Type where
  show TBool = "bool"
  show TInt = "int"
  show (TClosure t1 t2) = "(" ++ show t1 ++ " => " ++ show t2 ++ ")"
  show (TFun     t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (TVar x) = x

instance Expr.FreeVars Type where
  freeVars TBool = []
  freeVars TInt = []
  freeVars (TClosure t1 t2) = List.union (Expr.freeVars t1) (Expr.freeVars t2)
  freeVars (TFun     t1 t2) = List.union (Expr.freeVars t1) (Expr.freeVars t2)
  freeVars (TVar x) = [x]

instance Expr.FreeVars TypeSchema where
  freeVars (TSType ty) = Expr.freeVars ty
  freeVars (TSForall x ty) = List.delete x (Expr.freeVars ty)

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
  let extractFromTySchema (TSType ty) = Expr.freeVars ty
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
applyOnType s TBool = TBool
applyOnType s TInt = TInt
applyOnType s (TClosure t1 t2) = TClosure (applyOnType s t1) (applyOnType s t2)
applyOnType s (TFun     t1 t2) = TFun     (applyOnType s t1) (applyOnType s t2)
applyOnType s (TVar x) = Maybe.fromMaybe (TVar x) (List.lookup x s)

applyOnTypeSchema :: Subst -> TypeSchema -> TypeSchema
applyOnTypeSchema s (TSType ty) = TSType (applyOnType s ty)
applyOnTypeSchema s (TSForall x ts) = TSForall x (applyOnTypeSchema s ts)

applyOnContext :: Subst -> Context -> Context
applyOnContext s = map (\(x, tySchema) -> (x, applyOnTypeSchema s tySchema))

concatSubst :: Subst -> Subst -> Subst
concatSubst as bs = map (\(x, ty) -> (x, applyOnType bs ty)) as ++ bs

genFreshTVar :: Monad m => NameGenT m Type
genFreshTVar = fresh >>= (return . TVar)

typeContains :: String -> Type -> Bool
typeContains x TBool = False
typeContains x TInt = False
typeContains x (TClosure t1 t2) = (typeContains x t1) || (typeContains x t2)
typeContains x (TFun     t1 t2) = (typeContains x t1) || (typeContains x t2)
typeContains x (TVar y) = x == y

unify :: Type -> Type -> Maybe Subst
unify (TVar x) (TVar y) = Just $
  if x == y then emptySubst else singletonSubst (x, TVar y)
unify (TVar x) t =
  if typeContains x t then Nothing else Just (singletonSubst (x, t))
unify t (TVar x) =
  if typeContains x t then Nothing else Just (singletonSubst (x, t))
unify (TClosure t1 t2) (TClosure t1' t2') = do
  s1 <- unify t1 t1'
  s2 <- unify (applyOnType s1 t2) (applyOnType s1 t2')
  Just (concatSubst s1 s2)
unify (TClosure t1 t2) (TFun t1' t2') = do
  s1 <- unify t1 t1'
  s2 <- unify (applyOnType s1 t2) (applyOnType s1 t2')
  Just (concatSubst s1 s2)
unify (TFun t1 t2) (TClosure t1' t2') = do
  s1 <- unify t1 t1'
  s2 <- unify (applyOnType s1 t2) (applyOnType s1 t2')
  Just (concatSubst s1 s2)
unify (TFun t1 t2) (TFun t1' t2') = do
  s1 <- unify t1 t1'
  s2 <- unify (applyOnType s1 t2) (applyOnType s1 t2')
  Just (concatSubst s1 s2)
unify x y = if x == y then Just emptySubst else Nothing

infer :: Context -> Expr -> Maybe (Subst, Type, TyExpr Type)
infer c e = runNameGenTWithout (extractTypeVars c) (impl c e)
  where cat = concatSubst
        app = applyOnContext

        checkBinOpElements
          :: (TyExpr Type -> TyExpr Type -> TyExpr Type) -- ^ The type constructor
          -> Type    -- ^ The type of the left hand side
          -> Type    -- ^ The type of the right hand side
          -> Type    -- ^ The type of the resulting expression
          -> Context -- ^ Context in which the expressions are type-checked
          -> Expr  -- ^ Left hand side expression
          -> Expr  -- ^ Right hand side expression
          -> NameGenT Maybe (Subst, Type, TyExpr Type)
        checkBinOpElements op t1 t2 t c e1 e2 = do
          (s1, tau1, e1') <- impl c e1
          s1' <- lift (unify tau1 t1)
          let s1'' = s1 `cat` s1'
          (s2, tau2, e2') <- impl (s1'' `app` c) e2
          s2' <- lift (unify tau2 t2)
          return (s1'' `cat` s2 `cat` s2', t, op e1' e2')

        impl :: Context -> Expr -> NameGenT Maybe (Subst, Type, TyExpr Type)
        impl c (Var x) = do
          let instanciate :: Monad m => Subst -> TypeSchema -> NameGenT m Type
              instanciate s (TSType ty) = return (applyOnType s ty)
              instanciate s (TSForall x tySchema) = do
                alpha <- genFreshTVar
                instanciate (addSubst (x, alpha) s) tySchema
          tySchema <- lift (lookupContext x c)
          newType <- instanciate emptySubst tySchema
          return (emptySubst, newType, Var x)
        impl c (ExternVar x) = do
          return (emptySubst, TFun TInt TInt, ExternVar x)
        impl c abs@(Abs (x, _) e) = do
          alpha <- genFreshTVar
          (s, tau, e') <- impl (addContext (x, alpha) c) e
          let alpha' = applyOnType s alpha
          let ty = case Expr.freeVars abs of
                     []  -> TFun alpha' tau
                     (_:_) -> TClosure alpha' tau
          return (s, ty, Abs (x, ty) e')
        impl c (App e1 e2) = do
          (s1, tau1, e1') <- impl c e1
          (s2, tau2, e2') <- impl (s1 `app` c) e2
          beta <- genFreshTVar
          s3 <- lift $ unify (applyOnType s2 tau1) (TClosure tau2 beta)
          return (s1 `cat` s2 `cat` s3, applyOnType s3 beta, App e1' e2')
        impl c (LitInt n) = return (emptySubst, TInt, LitInt n)
        impl c (LitBool b) = return (emptySubst, TBool, LitBool b)
        impl c (OpMul e1 e2) = checkBinOpElements OpMul TInt TInt TInt  c e1 e2
        impl c (OpDiv e1 e2) = checkBinOpElements OpDiv TInt TInt TInt  c e1 e2
        impl c (OpAdd e1 e2) = checkBinOpElements OpAdd TInt TInt TInt  c e1 e2
        impl c (OpSub e1 e2) = checkBinOpElements OpSub TInt TInt TInt  c e1 e2
        impl c (OpLT  e1 e2) = checkBinOpElements OpLT  TInt TInt TBool c e1 e2
        impl c (OpEQ  e1 e2) = checkBinOpElements OpEQ  TInt TInt TBool c e1 e2
        impl c (If e e1 e2) = do
          (s1, tau, e') <- impl c e
          s2 <- lift $ unify tau TBool
          let s3 = s1 `cat` s2
          (theta1, tau1, e1') <- impl (s3 `app` c) e1
          (theta2, tau2, e2') <- impl ((theta1 `cat` s3) `app` c) e2
          theta3 <- lift $ unify (applyOnType theta2 tau1) tau2
          return (s3 `cat` theta1 `cat` theta2 `cat` theta3,
            applyOnType theta3 tau2, If e' e1' e2')
        impl c (Let x e1 e2) = do
          (theta1, tau1, e1') <- impl c e1
          let theta1' = theta1 `app` c
          let fv = Expr.freeVars tau1
          let tyVars = fv \\ (extractTypeVars theta1')
          let tau1' = List.foldl (flip TSForall) (TSType tau1) tyVars
          (theta2, tau2, e2') <- impl (addTySchemaToContext (x, tau1') theta1') e2
          return (theta1 `cat` theta2, tau2, Let x e1' e2')
        impl c (LetRec f ((y, ty), e1) e2) = do
          alpha <- genFreshTVar
          (theta1, tau1, Abs (y', ty') e1') <-
            impl (addContext (f, alpha) c) (Abs (y, ty) e1)
          s <- lift (unify (applyOnType theta1 alpha) tau1)
          let theta1' = theta1 `app` c
          let fv = Expr.freeVars tau1
          let tyVars = fv \\ (extractTypeVars (s `app` theta1'))
          let tau1' = List.foldl (flip TSForall) (TSType tau1) tyVars
          (theta2, tau2, e2') <-
            impl (s `app` (addTySchemaToContext (f, tau1') theta1')) e2
          return (theta1 `cat` s `cat` theta2, tau2,
            LetRec f ((y', ty'), e1') e2')

inferProgType :: Expr -> Maybe (TyExpr Type, Type)
inferProgType = fmap (\(a, b, c) -> (c, b)) . infer emptyContext
