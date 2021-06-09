module BindingRules (findSubstitution, hasFree, checkSubstitution) where

import Data
import Data.Maybe (isNothing)
import Data.Set (Set, union, singleton, empty, toList)

type Bindings = Var -> Bool
addBinding :: Var -> Bindings -> Bindings
addBinding v b v' = v == v' || b v'
emptyBinding :: Bindings
emptyBinding v = False

type SubstitutionResult = Maybe (Maybe Term)
type Finder a = Var -> Bindings -> a -> a -> SubstitutionResult
findBinarySubstitution' :: Finder a -> Var -> Bindings -> a -> a -> a -> a -> SubstitutionResult
findBinarySubstitution' finder var b l r l' r' =
  let sl = finder var b l l'
      sr = finder var b r r'
  in case (sl, sr) of
    (Just (Just lt), Just (Just rt)) ->
      if lt == rt then Just (Just lt) else Nothing
    (Just Nothing, Just (Just rt)) -> Just (Just rt)
    (Just (Just lt), Just Nothing) -> Just (Just lt)
    (Just Nothing, Just Nothing) -> Just Nothing
    _ -> Nothing

findBinarySubstitutionExpr' = findBinarySubstitution' findSubstitutionExpr'
findBinarySubstitutionTerm' = findBinarySubstitution' findSubstitutionTerm'

findSubstitutionExpr' :: Var -> Bindings -> Expr -> Expr -> SubstitutionResult
findSubstitutionExpr' var b (Impl l r) (Impl l' r') = findBinarySubstitutionExpr' var b l r l' r'
findSubstitutionExpr' var b (Or l r) (Or l' r') = findBinarySubstitutionExpr' var b l r l' r'
findSubstitutionExpr' var b (And l r) (And l' r') = findBinarySubstitutionExpr' var b l r l' r'
findSubstitutionExpr' var b (Not e) (Not e') = findSubstitutionExpr' var b e e'
findSubstitutionExpr' var b (Forall lv l) (Forall rv r)
  | lv == rv = findSubstitutionExpr' var (addBinding lv b) l r
  | otherwise = Nothing
findSubstitutionExpr' var b (Exists lv l) (Exists rv r)
  | lv == rv = findSubstitutionExpr' var (addBinding lv b) l r
  | otherwise = Nothing
findSubstitutionExpr' var b (ExprPred lp) (ExprPred rp) = findSubstitutionPred' var b lp rp
findSubstitutionExpr' _ _ _ _ = Nothing

findSubstitutionPred' :: Var -> Bindings -> Pred -> Pred -> SubstitutionResult
findSubstitutionPred' var b (Pred l) (Pred r) = if l == r then Just Nothing else Nothing
findSubstitutionPred' var b (PredEq l r) (PredEq l' r') = findBinarySubstitutionTerm' var b l r l' r'
findSubstitutionPred' _ _ _ _ = Nothing

findSubstitutionTerm' :: Var -> Bindings -> Term -> Term -> SubstitutionResult
findSubstitutionTerm' var b (Plus l r) (Plus l' r') = findBinarySubstitutionTerm' var b l r l' r'
findSubstitutionTerm' var b (Times l r) (Times l' r') = findBinarySubstitutionTerm' var b l r l' r'
findSubstitutionTerm' var b (Succ l) (Succ r) = findSubstitutionTerm' var b l r
findSubstitutionTerm' var b Zero Zero = Just Nothing
findSubstitutionTerm' var b l@(TermVar v) r
  | var == v = if b v
    then if l /= r then Nothing else Just Nothing
    else Just $ Just r
  | otherwise = if l /= r
    then Nothing
    else Just Nothing
findSubstitutionTerm' _ _ _ _ = Nothing


findSubstitution ::
  Var ->
  -- | The expression without substitution
  Expr ->
  -- | The expression with substitution
  Expr ->
  SubstitutionResult
findSubstitution var = findSubstitutionExpr' var emptyBinding


hasFree :: Var -> Expr -> Bool
hasFree var e = findSubstitution var e e == Just Nothing


getVars :: Term -> Set Var
getVars (Plus l r) = getVars l `union` getVars r
getVars (Times l r) = getVars l `union` getVars r
getVars (Succ e) = getVars e
getVars (TermVar v) = singleton v
getVars Zero = empty

checkSubstitution :: Var -> Term -> Expr -> Bool
checkSubstitution = checkSubstitutionExpr' emptyBinding

type Checker a = (Bindings -> Var -> Term -> a -> Bool)
checkSubstitutionAll' :: Checker a -> Bindings -> Var -> Term -> [a] -> Bool
checkSubstitutionAll' checker b var t = all (checker b var t)

checkSubstitutionExpr' :: Bindings -> Var -> Term -> Expr -> Bool
checkSubstitutionExpr' b var t (Impl l r) = checkSubstitutionAll' checkSubstitutionExpr' b var t [l ,r]
checkSubstitutionExpr' b var t (Or l r) = checkSubstitutionAll' checkSubstitutionExpr' b var t [l ,r]
checkSubstitutionExpr' b var t (And l r) = checkSubstitutionAll' checkSubstitutionExpr' b var t [l ,r]
checkSubstitutionExpr' b var t (Not e) = checkSubstitutionExpr' b var t e
checkSubstitutionExpr' b var t (Forall v l) = checkSubstitutionExpr' (addBinding v b) var t l
checkSubstitutionExpr' b var t (Exists v l) = checkSubstitutionExpr' (addBinding v b) var t l
checkSubstitutionExpr' b var t (ExprPred e) = checkSubstitutionPred' b var t e

checkSubstitutionPred' :: Bindings -> Var -> Term -> Pred -> Bool
checkSubstitutionPred' _ _ _ (Pred _) = True
checkSubstitutionPred' b var t (PredEq l r) = checkSubstitutionAll' checkSubstitutionTerm' b var t [l, r]

checkSubstitutionTerm' :: Bindings -> Var -> Term -> Term -> Bool
checkSubstitutionTerm' b var t (Plus l r) = checkSubstitutionAll' checkSubstitutionTerm' b var t [l, r]
checkSubstitutionTerm' b var t (Times l r) = checkSubstitutionAll' checkSubstitutionTerm' b var t [l, r]
checkSubstitutionTerm' b var t (Succ e) = checkSubstitutionTerm' b var t e
checkSubstitutionTerm' b var t Zero = True
checkSubstitutionTerm' b var t (TermVar v) = v /= var || (b v || not (any b $ toList $ getVars t))
