{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module TypeInference2 where

import qualified Data.List as List
import qualified Data.Set as Set

import Control.Monad((<=<))
import Control.Monad.Trans(lift)
import Data.Bifunctor(bimap)
import Data.Set(Set)
import Expr
import FreshName

-- Simple types and annotations (Principles of Program Analysis, p. 306)

newtype TVar = TVar String deriving (Eq, Ord, Show)
newtype AVar = AVar String deriving (Eq, Ord, Show)
data SType = STInt | STBool | STFun AVar SType SType | STVar TVar deriving (Eq, Show)
data SAnn a = SASingleton a | SAUnion (SAnn a) (SAnn a) | SAEmpty | SAVar AVar
  deriving (Eq, Ord)

{-
instance Show SType where
  show STBool = "bool"
  show STInt = "int"
  show (STFun _ t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (STVar (TVar x)) = x
-}

-- Unification of simple types (Principles of Program Analysis, p. 307)

type SSubst = (TVar -> Maybe SType, AVar -> AVar)

substId :: SSubst
substId = (const Nothing, id)

mapTVar :: (TVar -> Maybe SType) -> SType -> SType
mapTVar f STInt = STInt
mapTVar f STBool = STBool
mapTVar f (STFun b t1 t2) = STFun b (mapTVar f t1) (mapTVar f t2)
mapTVar f var@(STVar x) = maybe var id (f x)

substCompose :: SSubst -> SSubst -> SSubst
substCompose (f1, g1) (f2, g2) = (fmap (mapTVar f1) . f2 , g1 . g2)

substApplyTy :: SSubst -> SType -> SType
substApplyTy s@(f, g) STInt = STInt
substApplyTy s@(f, g) STBool = STBool
substApplyTy s@(f, g) (STFun b t1 t2) =
  STFun (g b) (substApplyTy s t1) (substApplyTy s t2)
substApplyTy s@(f, g) var@(STVar x) = maybe var id (f x)

substApplyAnn :: SSubst -> AVar -> AVar
substApplyAnn = snd

substTy :: TVar -> SType -> SSubst
substTy x ty = (\y -> if x == y then Just ty else Nothing, id)

substAnn :: AVar -> AVar -> SSubst
substAnn x ann = (const Nothing, \y -> if x == y then ann else y)

occursIn x ty =
  case ty of
    STInt -> False
    STBool -> False
    (STFun _ t1 t2) -> occursIn x t1 || occursIn x t2
    (STVar y) -> x == y

unify :: SType -> SType -> Maybe SSubst
unify STInt STInt = return substId
unify STBool STBool = return substId
unify (STFun b t1 t2) (STFun b' t1' t2') = do
  let app = substApplyTy
  let o = substCompose
  s0 <- return (substAnn b' b)
  s1 <- unify (app s0 t1) (app s0 t1')
  s2 <- unify (app s1 (app s0 t1)) (app s1 (app s0 t1'))
  return (s2 `o` s1 `o` s0)
unify t alpha@(STVar x) =
  if t == alpha || not (occursIn x t) then return (substTy x t) else Nothing
unify alpha@(STVar x) t = unify t alpha
unify t1 t2 = Nothing

-- Constraints (Principles of Program Analysis, p. 308)

newtype Constraint = Constraint (AVar, SAnn ()) deriving (Eq, Ord)

substApplyConstraint :: SSubst -> Constraint -> Constraint
substApplyConstraint s (Constraint (x, ann)) =
  Constraint (substApplyAnn s x, ann)

substApplyConstraints :: SSubst -> Set Constraint -> Set Constraint
substApplyConstraints = Set.map . substApplyConstraint

-- The algorithm (Principles of Program Analysis, p. 309)

type Context = [(String, SType)]
type TyExpr = Expr SType SType

substApplyCtxt :: SSubst -> Context -> Context
substApplyCtxt s = map (\(x, ty) -> (x, substApplyTy s ty))

freshSTVar :: Monad m => NameGenT m SType
freshSTVar = fmap (STVar . TVar) fresh

freshAVar :: Monad m => NameGenT m AVar
freshAVar = fmap AVar fresh

freeVars :: SType -> Set TVar
freeVars STInt = Set.empty
freeVars STBool = Set.empty
freeVars (STFun _ t1 t2) = Set.union (freeVars t1) (freeVars t2)
freeVars (STVar x) = Set.singleton x

checkBinOp
  :: (SType -> TyExpr -> TyExpr -> TyExpr)  -- ^ The constructor
  -> SType       -- ^ The type of the left hand side
  -> SType       -- ^ The type of the right hand side
  -> SType       -- ^ The type of the resulting expression
  -> Context    -- ^ Context in which the expressions are type-checked
  -> Expr () () -- ^ Left hand side expression
  -> Expr () () -- ^ Right hand side expression
  -> NameGenT Maybe (TyExpr, SSubst, Set Constraint)
checkBinOp con t1 t2 t c e1 e2 = do
  (e1', s1, cs1) <- inferImpl c e1
  (e2', s2, cs2) <- inferImpl c e2
  let e1Ty = Expr.getType e1'
  let e2Ty = Expr.getType e2'
  s3 <- lift (unify (substApplyTy s2 e1Ty) t1)
  s4 <- lift (unify (substApplyTy s3 e2Ty) t2)
  let o = substCompose
  let substs = s4 `o` s3 `o` s2 `o` s1
  let app = substApplyConstraints
  let cs = Set.union
        (s4 `app` (s3 `app` (s2 `app` (s1 `app` cs1))))
        (s4 `app` (s3 `app` cs1))
  return (con t e1' e2', substs, cs)

inferImpl :: Context -> Expr () ()
  -> NameGenT Maybe (TyExpr, SSubst, Set Constraint)
inferImpl c (LitInt _ n) = return (LitInt STInt n, substId, Set.empty)
inferImpl c (LitBool _ b) = return (LitBool STBool b, substId, Set.empty)
inferImpl c (Var _ x) = do
  ty <- lift (List.lookup x c)
  return (Var ty x, substId, Set.empty)
inferImpl c (ExternVar _ x) = do
  beta <- freshAVar
  let c = Constraint (beta, SAEmpty)
  return (ExternVar (STFun beta STInt STInt) x, substId, Set.singleton c)
inferImpl c (Abs _ x e) = do
  alpha <- freshSTVar
  (e', s, cs) <- inferImpl ((x, alpha) : c) e
  beta <- freshAVar
  let tau = STFun beta (substApplyTy s alpha) (Expr.getType e')
  let cs' = Set.insert (Constraint (beta, SAEmpty)) cs
  return (Abs tau x e', s, cs')
inferImpl c (App _ e1 e2) = do
  let app = substApplyConstraints
  let o = substCompose
  (e1', s1, cs1) <- inferImpl c e1
  (e2', s2, cs2) <- inferImpl (substApplyCtxt s1 c) e2
  alpha <- freshSTVar
  beta <- freshAVar
  s3 <- lift $ unify
    (substApplyTy s2 (Expr.getType e1')) (STFun beta (Expr.getType e2') alpha)
  let cs = Set.union (app s3 (app s2 cs1)) (app s3 cs2)
  return (App (substApplyTy s3 alpha) e1' e2', s3 `o` s2 `o` s1, cs)
inferImpl c (If _ e0 e1 e2) = do
  (e0', s0, cs0) <- inferImpl c e0
  let c = substApplyCtxt s0 c
  (e1', s1, cs1) <- inferImpl c e1
  let c = substApplyCtxt s1 c
  (e2', s2, cs2) <- inferImpl c e2
  let ty0 = Expr.getType e0'
  let ty1 = Expr.getType e1'
  let ty2 = Expr.getType e2'
  s3 <- lift $ unify (substApplyTy s2 (substApplyTy s1 ty0)) STBool
  s4 <- lift $ unify (substApplyTy s3 ty1) (substApplyTy s3 (substApplyTy s2 ty2))
  let ty = substApplyTy s4 (substApplyTy s3 ty2)
  let o = substCompose
  let s = s4 `o` s3 `o` s2 `o` s1
  let app = substApplyConstraints
  let cs0' = s4 `app` (s3 `app` (s2 `app` (s1 `app` cs0)))
  let cs1' = s4 `app` (s3 `app` (s2 `app` cs1))
  let cs2' = s4 `app` (s3 `app` cs2)
  let cs = cs0' `Set.union` cs1' `Set.union` cs2'
  return (If ty e0' e1' e2', s, cs)
inferImpl c (Let _ (x, _) e1 e2) = do
  (e1', s1, cs1) <- inferImpl c e1
  let ty1 = Expr.getType e1'
  --let fv = freeVars ty1
  (e2', s2, cs2) <- inferImpl ((x, ty1) : substApplyCtxt s1 c) e2
  let ty2 = Expr.getType e2'
  let substs = substCompose s2 s1
  let cs = Set.union (substApplyConstraints s2 cs1) cs2
  return (Let ty2 (x, ty1) e1' e2', substs, cs)
inferImpl c (LetRec _ (f, _) (x, e1) e2) = do
  xTy <- freshSTVar
  yTy <- freshSTVar
  b <- freshAVar
  (e1', s1, cs1) <- inferImpl ((f, STFun b xTy yTy) : (x, xTy) : c) e1
  let e1Ty = Expr.getType e1'
  s1' <- lift (unify e1Ty (substApplyTy s1 yTy))
  let appTy = substApplyTy
  let appAn = substApplyAnn
  let b' = (s1' `appAn` (s1 `appAn` b))
  let fTy = STFun b' (s1' `appTy` (s1 `appTy` xTy)) (s1' `appTy` e1Ty)
  let fSubst = substCompose s1' s1
  let fCs = Set.insert (Constraint (b', SAEmpty)) (substApplyConstraints s1' cs1)
  (e2', s2, cs2) <- inferImpl ((f, fTy) : substApplyCtxt fSubst c) e2
  let ty2 = Expr.getType e2'
  let substs = substCompose s2 s1
  let cs = Set.union (substApplyConstraints s2 fCs) cs2
  return (LetRec ty2 (f, fTy) (x, e1') e2', substs, cs)
inferImpl c (OpMul _ e1 e2) = checkBinOp OpMul STInt STInt STInt  c e1 e2
inferImpl c (OpDiv _ e1 e2) = checkBinOp OpDiv STInt STInt STInt  c e1 e2
inferImpl c (OpAdd _ e1 e2) = checkBinOp OpAdd STInt STInt STInt  c e1 e2
inferImpl c (OpSub _ e1 e2) = checkBinOp OpSub STInt STInt STInt  c e1 e2
inferImpl c (OpLT  _ e1 e2) = checkBinOp OpLT  STInt STInt STBool c e1 e2
inferImpl c (OpEQ  _ e1 e2) = checkBinOp OpEQ  STInt STInt STBool c e1 e2

infer :: Context -> Expr () () -> Maybe (SSubst, TyExpr)
infer c e = do
  case runNameGenTWithout [] (inferImpl c e) of
    Nothing -> Nothing
    Just (expr, s, _) -> let sub = substApplyTy s in Just (s, bimap sub sub expr)
