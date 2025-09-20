{-# OPTIONS_GHC -Wno-deferred-type-errors #-}
module ProofChecker (annotate) where

import Data
import Annotation
import BindingRules
import Helpers
import Data.Maybe (mapMaybe, isJust)
import Data.Map (Map, empty, mapWithKey)
import qualified Data.Map as M
import Control.Applicative ((<|>))


annotate :: File -> Either AnnotationErrorFile AnnotatedFile
annotate (File e es) =
  let (aes, err) = annotateExprs e es
  in case err of
    Just err -> Left $ AnnotationErrorFile (AnnotatedFile e aes) err
    Nothing -> Right $ AnnotatedFile e aes

annotateExprs :: Expr -> [Expr] -> ([AnnotatedExpr], Maybe AnnotationError)
annotateExprs e es' =
  let (es, err) = annotateExprs' 1 empty es'
  in case err of
    Just e -> (es, err)
    Nothing ->
      if getExpr (last es) /= e
      then (es, Just WrongExpressionProved)
      else (es, Nothing)

annotateExprs' :: Int -> Map Expr Int -> [Expr] -> ([AnnotatedExpr], Maybe AnnotationError)
annotateExprs' n prev (e:es) =
  case checkScheme n e
       <?> checkAxiom n e
       <?> checkRules n prev e
  of
    Left err -> ([], Just err)
    Right Nothing -> ([], Just $ NotProved n)
    -- Right Nothing ->
    --   let (aes, err) = annotateExprs' (n + 1) (M.insertWith min e n prev) es
    --   in (((AnnotatedExpr e $ ExistsRule 0 0)) : aes, err)
    Right (Just ae) ->
      let (aes, err) = annotateExprs' (n + 1) (M.insertWith min e n prev) es
      in (ae : aes, err)
annotateExprs' _ _ [] = ([], Nothing)


checkScheme :: Int -> Expr -> Either AnnotationError (Maybe AnnotatedExpr)
checkScheme n e =
  case mapMaybe (checkSimpleScheme' e) $ zip [1..]
               [ checkScheme1
               , checkScheme2
               , checkScheme3
               , checkScheme4
               , checkScheme5
               , checkScheme6
               , checkScheme7
               , checkScheme8
               , checkScheme9
               , checkScheme10]
  of
    (s:_) -> Right $ Just $ AnnotatedExpr e $ AxiomScheme n $ Number s
    [] ->  checkSchemeForall n e
           <?> checkSchemeExists n e
           <?> checkSchemeInduction n e
    where
      checkSimpleScheme' :: Expr -> (Int, Expr -> Bool) -> Maybe Int
      checkSimpleScheme' e (n, checker) = if checker e then Just n else Nothing

checkScheme1 (Impl alpha (Impl beta alpha')) =
    alpha == alpha'
checkScheme1 _ = False
checkScheme2 (Impl (Impl alpha beta) (Impl (Impl alpha' (Impl beta' gamma)) (Impl alpha'' gamma'))) =
    alpha == alpha' && alpha' == alpha'' && beta == beta' && gamma == gamma'
checkScheme2 _ = False
checkScheme3 (Impl alpha (Impl beta (And alpha' beta'))) =
    alpha == alpha' && beta == beta'
checkScheme3 _ = False
checkScheme4 (Impl (And alpha beta) alpha') =
    alpha == alpha'
checkScheme4 _ = False
checkScheme5 (Impl (And alpha beta) beta') =
    beta == beta'
checkScheme5 _ = False
checkScheme6 (Impl alpha (Or alpha' beta)) =
    alpha == alpha'
checkScheme6 _ = False
checkScheme7 (Impl beta (Or alpha beta')) =
    beta == beta'
checkScheme7 _ = False
checkScheme8 (Impl (Impl alpha gamma) (Impl (Impl beta gamma') (Impl (Or alpha' beta') gamma''))) =
    alpha == alpha' && beta == beta' && gamma == gamma' && gamma' == gamma''
checkScheme8 _ = False
checkScheme9 (Impl (Impl alpha beta) (Impl (Impl alpha' (Not beta')) (Not alpha''))) =
    alpha == alpha' && alpha' == alpha'' && beta == beta'
checkScheme9 _ = False
checkScheme10 (Impl (Not (Not alpha)) alpha') =
    alpha == alpha'
checkScheme10 _ = False

checkSubstitutionScheme :: (Var -> Term -> AnnotationError) -> AnnotatedExpr -> Var -> Expr -> Expr -> Either AnnotationError (Maybe AnnotatedExpr)
checkSubstitutionScheme errF ae x phi phi' =
  case findSubstitution x phi phi' of
    Just (Just t) -> checkSubstitution' x t phi
    Just Nothing -> Right $ Just ae
    Nothing -> Right Nothing
  where
    checkSubstitution' var t e =
      if checkSubstitution var t e
      then Right $ Just ae
      else Left $ errF var t

checkSchemeForall :: Int -> Expr -> Either AnnotationError (Maybe AnnotatedExpr)
checkSchemeForall n e@(Impl (Forall x phi) phi') = checkSubstitutionScheme (NonFreeForallAxiom n) (AnnotatedExpr e $ AxiomScheme n $ Number 11) x phi phi'
checkSchemeForall _ _ = Right Nothing

checkSchemeExists :: Int -> Expr -> Either AnnotationError (Maybe AnnotatedExpr)
checkSchemeExists n e@(Impl phi' (Exists x phi)) = checkSubstitutionScheme (NonFreeExistsAxiom n) (AnnotatedExpr e $ AxiomScheme n $ Number 12) x phi phi'
checkSchemeExists _ _ = Right Nothing

checkSchemeInduction :: Int -> Expr -> Either AnnotationError (Maybe AnnotatedExpr)
checkSchemeInduction n e@(Impl (And phi0 (Forall x (Impl phi phi'))) phi'') =
  if phi'' == phi
  then case (findSubstitution x phi phi0, findSubstitution x phi phi') of
         (Just (Just Zero), Just (Just (Succ (TermVar x')))) -> Right $ Just $ AnnotatedExpr e $ AxiomScheme n $ ArithmeticNumber 9
         _ -> Right Nothing
  else Right Nothing
checkSchemeInduction _ _ = Right Nothing

checkAxiom :: Int -> Expr -> Either AnnotationError (Maybe AnnotatedExpr)
checkAxiom n e =
  case mapMaybe (applyAxiom e) $ zip [1..]
       [ axiom1
       , axiom2
       , axiom3
       , axiom4
       , axiom5
       , axiom6
       , axiom7
       , axiom8 ]
  of
    (a:_) -> Right $ Just $ AnnotatedExpr e $ ArithmeticAxiom n $ ArithmeticNumber a
    [] -> Right Nothing
  where
    applyAxiom e (n, ax) = if ax e then Just n else Nothing

axiom1 (Impl (ExprPred (PredEq (TermVar a) (TermVar b))) (ExprPred (PredEq (Succ (TermVar a')) (Succ (TermVar b'))))) =
  a == a' && b == b' && a == Var "a" && b == Var "b"
axiom1 _ = False
axiom2 (Impl (ExprPred (PredEq (TermVar a) (TermVar b))) (Impl (ExprPred (PredEq (TermVar a') (TermVar c))) (ExprPred (PredEq (TermVar b') (TermVar c'))))) =
  a == a' && b == b' && c == c' && a == Var "a" && b == Var "b" && c == Var "c"
axiom2 _ = False
axiom3 (Impl (ExprPred (PredEq (Succ (TermVar a)) (Succ (TermVar b)))) (ExprPred (PredEq (TermVar a') (TermVar b')))) =
  a == a' && b == b' && a == Var "a" && b == Var "b"
axiom3 _ = False
axiom4 (Not (ExprPred (PredEq (Succ (TermVar (Var "a"))) Zero))) = True
axiom4 _ = False
axiom5 (ExprPred (PredEq (Plus (TermVar a) (Succ (TermVar b))) (Succ (Plus (TermVar a') (TermVar b'))))) =
  a == a' && b == b' && a == Var "a" && b == Var "b"
axiom5 _ = False
axiom6 (ExprPred (PredEq (Plus (TermVar a) Zero) (TermVar a'))) =
  a == a' && a == Var "a"
axiom6 _ = False
axiom7 (ExprPred (PredEq (Times (TermVar (Var "a")) Zero) Zero)) = True
axiom7 _ = False
axiom8 (ExprPred (PredEq (Times (TermVar a) (Succ (TermVar b))) (Plus (Times (TermVar a') (TermVar b')) (TermVar a'')))) =
  a == a' && a' == a'' && b == b' && a == Var "a" && b == Var "b"
axiom8 _ = False

checkRules :: Int -> Map Expr Int -> Expr -> Either AnnotationError (Maybe AnnotatedExpr)
checkRules n es e = checkModusPonens n es e
                    <?> checkExistsRule n es e
                    <?> checkForallRule n es e

checkModusPonens :: Int -> Map Expr Int -> Expr  -> Either AnnotationError (Maybe AnnotatedExpr)
checkModusPonens n es e =
  let es' = M.mapMaybeWithKey (check' e es) es
  in case findMin es' of
    Just (_, (k, l)) -> Right $ Just $ AnnotatedExpr e $ ModusPonens n k l
    Nothing -> Right Nothing
  where
    check' :: Expr -> Map Expr Int -> Expr -> Int -> Maybe (Int, Int)
    check' e es (Impl e1 e') l =
      if e == e'
      then case M.lookup e1 es of
             Just k -> Just (k, l)
             Nothing -> Nothing
      else Nothing
    check' _ _ _ _ = Nothing

checkExistsRule :: Int -> Map Expr Int -> Expr -> Either AnnotationError (Maybe AnnotatedExpr)
checkExistsRule n es e@(Impl (Exists x psi) phi) =
  case M.lookup (Impl psi phi) es of
    Just k -> if hasFree x phi
              then Right $ Just (AnnotatedExpr e $ ExistsRule n k)
              else Left $ NonFreeExists n x
    Nothing -> Right Nothing
checkExistsRule _ _ _ = Right Nothing

checkForallRule :: Int -> Map Expr Int -> Expr -> Either AnnotationError (Maybe AnnotatedExpr)
checkForallRule n es e@(Impl phi (Forall x psi)) =
  case M.lookup (Impl phi psi) es of
    Just k -> if hasFree x phi
              then Right $ Just (AnnotatedExpr e $ ForallRule n k)
              else Left $ NonFreeForall n x
    Nothing -> Right Nothing
checkForallRule _ _ _ = Right Nothing
