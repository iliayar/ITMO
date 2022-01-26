module Util where

import Proof
import qualified Data.Map as M
import Control.Monad.State
import qualified Data.Set as S

ctxLookup :: Var -> Context -> Maybe Type
ctxLookup v (Context m) = M.lookup v m

ctxInsert :: Var -> Type -> Context -> Context
ctxInsert v t (Context m) = Context $ M.insert v t m

ctxFindTypeFree :: Context -> S.Set TypeVar
ctxFindTypeFree (Context m) = M.foldlWithKey' (\s _ t -> S.union s $ findTypeFree t) S.empty m

findTypeFree :: Type -> S.Set TypeVar
findTypeFree t = evalState (findTypeFree' t) S.empty
  where
    findTypeFree' :: Type -> State (S.Set TypeVar) (S.Set TypeVar)
    findTypeFree' (TypeForall v t) = do
      modify $ S.insert v
      findTypeFree' t
    findTypeFree' (TypeMonoType t) = findMonoTypeFree' t

    findMonoTypeFree' :: MonoType -> State (S.Set TypeVar) (S.Set TypeVar)
    findMonoTypeFree' (MonoTypeVar v) = do
      c <- gets $ S.member v
      pure $ if c then S.empty else S.singleton v
    findMonoTypeFree' (l :->: r) = do
      ls <- findMonoTypeFree' l
      rs <- findMonoTypeFree' r
      pure $ S.union ls rs

checkSubtype :: Type -> Type -> Bool
checkSubtype t1 t2 =
  let
    (as, mt1) = trunkSchema t1
    (bs, mt2) = trunkSchema t2
  in checkSubst mt1 mt2 && 0 == S.size (S.intersection (findTypeFree t1) bs)

trunkSchema :: Type -> (S.Set TypeVar, MonoType)
trunkSchema (TypeMonoType t) = (S.empty, t)
trunkSchema (TypeForall v t) =
  let (s, mt) = trunkSchema t
  in (S.insert v s, mt)

checkSubst :: MonoType -> MonoType -> Bool
checkSubst t1 t2 = evalState (checkSubst' t1 t2) M.empty
  where
    checkSubst' :: MonoType -> MonoType -> State (M.Map TypeVar MonoType) Bool
    checkSubst' (le1 :->: le2) (re1 :->: re2) = do
      r1 <- checkSubst' le1 re1
      r2 <- checkSubst' le2 re2
      pure $ r1 && r2
    checkSubst' (MonoTypeVar v) e = do
      e'' <- gets $ M.lookup v
      case e'' of
        Just e'
          | e' == e -> pure True
          | otherwise -> pure False
        Nothing -> do
          modify $ M.insert v e
          pure True
