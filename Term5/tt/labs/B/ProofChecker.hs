{-# OPTIONS_GHC -Wall #-}
module ProofChecker where

import Proof
import Util
import qualified Control.Monad.State as S
import qualified Data.Map as M
import qualified Data.Set as Set
import Control.Monad (guard)
import Data.Maybe (isJust)
import Debug.Trace (trace)

data CheckResult = Correct | Incorrect
  deriving (Show)

resFromBool :: Bool -> CheckResult
resFromBool True = Correct
resFromBool False = Incorrect

alphaEq :: Expression -> Expression -> Bool
alphaEq e1 e2 = S.evalState (alphaEq' e1 e2) M.empty
  where
    alphaEq' :: Expression -> Expression -> S.State (M.Map Var Var) Bool
    alphaEq' (vl :\: el) (vr :\: er) = do
      S.modify $ bindNew vl vr
      alphaEq' el er
    alphaEq' (ExpressionLetIn vl nl el) (ExpressionLetIn vr nr er) = do
      S.modify $ bindNew vl vr
      (&&) <$> alphaEq' el er <*> alphaEq' nl nr
    alphaEq' (el1 :@: el2) (er1 :@: er2) =
      (&&) <$> alphaEq' el1 er1 <*> alphaEq' el2 er2
    alphaEq' (ExpressionVar vr) (ExpressionVar vl) =
      S.gets $ alphaEqVar vr vl
    alphaEq' _ _ = pure False

    bindNew :: Var -> Var -> M.Map Var Var -> M.Map Var Var
    bindNew v1 v2 m = if v1 == v2 then m else
      let nv = Var $ "#" ++ show (M.size m)
      in M.insert v1 nv $ M.insert v2 nv m

    alphaEqVar :: Var -> Var -> M.Map Var Var -> Bool
    alphaEqVar v1 v2 m =
      case (M.lookup v1 m, M.lookup v2 m) of
        (Just rv1, Just rv2) -> rv1 == rv2
        (Nothing, Nothing ) -> v1 == v2
        _ -> False

typeEq :: Type -> Type -> Bool
typeEq e1 e2 = S.evalState (typeEq' e1 e2) M.empty
  where
    typeEq' :: Type -> Type -> S.State (M.Map TypeVar TypeVar) Bool
    typeEq' (TypeForall vl tl) (TypeForall vr tr) = do
      S.modify $ bindNew vl vr
      typeEq' tl tr
    typeEq' (TypeMonoType tl) (TypeMonoType tr) =
      monotypeEq' tl tr
    typeEq' _ _ = pure False

    monotypeEq' :: MonoType -> MonoType -> S.State (M.Map TypeVar TypeVar) Bool
    monotypeEq' (tl1 :->: tl2) (tr1 :->: tr2) = do
      (&&) <$> monotypeEq' tl1 tr1 <*> monotypeEq' tl2 tr2
    monotypeEq' (MonoTypeVar vl) (MonoTypeVar vr) = do
      S.gets $ typeEqVar vl vr
    monotypeEq' _ _ = pure False

    bindNew :: TypeVar -> TypeVar -> M.Map TypeVar TypeVar -> M.Map TypeVar TypeVar
    bindNew v1 v2 m = if v1 == v2 then m else
      let nv = TypeVar $ "#" ++ show (M.size m)
      in M.insert v1 nv $ M.insert v2 nv m

    typeEqVar :: TypeVar -> TypeVar -> M.Map TypeVar TypeVar -> Bool
    typeEqVar v1 v2 m =
      case (M.lookup v1 m, M.lookup v2 m) of
        (Just rv1, Just rv2) -> rv1 == rv2
        (Nothing, Nothing ) -> v1 == v2
        _ -> False

check :: Proof -> CheckResult
check = resFromBool . check'

check' :: Proof -> Bool
check' (Tree (Statement ctx ((ExpressionVar v) ::: t) (Rule 1)) []) = isJust $ do
  ct <- ctxLookup v ctx
  guard $ ct == t
check' (Tree (Statement ctx (e0 :@: e1 ::: (TypeMonoType t1)) (Rule 2))
      concl@[ Tree (Statement ctx1 (e0' ::: (TypeMonoType (t :->: t1'))) _) _
            , Tree (Statement ctx2 (e1' ::: (TypeMonoType t')) _) _]) =
  all check' concl && e0 == e0' && e1' == e1 && t1 == t1' && t == t' && ctx1 == ctx && ctx2 == ctx
check' (Tree (Statement ctx (x :\: e ::: (TypeMonoType (t :->: t1))) (Rule 3))
       concl@[ Tree (Statement ctx1 (e' ::: (TypeMonoType t1')) _) _]) =
  all check' concl && t1' == t1 && e' == e && not (ctxMember x ctx) && ctxInsert x (TypeMonoType t) ctx == ctx1
check' (Tree (Statement ctx (ExpressionLetIn x e0 e1 ::: (TypeMonoType t)) (Rule 4))
       concl@[ Tree (Statement ctx1 (e0' ::: sigma) _) _
             , Tree (Statement ctx2 (e1' ::: (TypeMonoType t')) _) _]) =
  all check' concl && e0' == e0 && e1' == e1 && t' == t && not (ctxMember x ctx) && ctxInsert x sigma ctx == ctx2 && ctx == ctx1
check' (Tree (Statement ctx (e ::: sigma) (Rule 5))
       concl@[ Tree (Statement ctx1 (e' ::: sigma') _) _]) =
  all check' concl && e == e' && checkSubtype sigma' sigma && ctx == ctx1
check' (Tree (Statement ctx (e ::: (TypeForall alpha sigma)) (Rule 6))
       concl@[ Tree (Statement ctx1 (e' ::: sigma') _) _]) =
  all check' concl && not (Set.member alpha $ ctxFindTypeFree ctx) && e' == e && sigma' == sigma && ctx1 == ctx
check' _ = False
