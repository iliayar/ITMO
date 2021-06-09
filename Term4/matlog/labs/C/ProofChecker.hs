{-# OPTIONS_GHC -Wno-deferred-type-errors #-}
module ProofChecker (annotate) where

import Data
import Annotation
import BindingRules
import Data.Maybe (mapMaybe)

annotate :: File -> Either AnnotationErrorFile AnnotatedFile
annotate (File e es) =
  let (aes, err) = annotateExprs es
  in case err of
    Just err -> Left $ AnnotationErrorFile (AnnotatedFile e aes) err
    Nothing -> Right $ AnnotatedFile e aes

annotateExprs :: [Expr] -> ([AnnotatedExpr], Maybe AnnotationError)
annotateExprs = annotateExprs' 1 []

annotateExprs' :: Int -> [Expr] -> [Expr] -> ([AnnotatedExpr], Maybe AnnotationError)
annotateExprs' n prev (e:es) =
  let ret ae = (let (aes, err) = annotateExprs' (n + 1) (e:prev) es in (ae : aes, err))
  in case checkScheme n e of
       Left err -> ([], Just err)
       Right (Just ae) -> ret ae
       Right Nothing ->
         case checkAxiom n e of
           Just ae -> ret ae
           Nothing ->
             case checkRules n (reverse prev) e of
               Left err -> ([], Just err)
               Right (Just ae) -> ret ae
               Right Nothing -> ([], Just $ NotProved n)
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
    [] -> case checkSchemeForall e of
            Right True -> Right $ Just $ AnnotatedExpr e $ AxiomScheme n $ Number 11
            Left (var, term) -> Left $ NonFreeForallAxiom n var term
            Right False ->
              case checkSchemeExists e of
                Right True -> Right $ Just $ AnnotatedExpr e $ AxiomScheme n $ Number 12
                Left (var, term) -> Left $ NonFreeExistsAxiom n var term
                Right False -> if checkSchemeInduction e
                               then Right $ Just $ AnnotatedExpr e $ AxiomScheme n $ ArithmeticNumber 9
                               else Right Nothing
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

checkSubstitutionScheme :: Int -> Var -> Expr -> Expr -> Either (Var, Term) Bool
checkSubstitutionScheme n x phi phi' =
  case findSubstitution x phi phi' of
    Just (Just t) -> checkSubstitution' x t phi
    Just Nothing -> Right True
    Nothing -> Right False
  where
    checkSubstitution' var t e =
      if checkSubstitution var t e
      then Right True
      else Left (var, t)

checkSchemeForall :: Expr -> Either (Var, Term) Bool
checkSchemeForall (Impl (Forall x phi) phi') = checkSubstitutionScheme 11 x phi phi'
checkSchemeForall _ = Right False

checkSchemeExists :: Expr -> Either (Var, Term) Bool
checkSchemeExists (Impl phi' (Exists x phi)) = checkSubstitutionScheme 12 x phi phi'
checkSchemeExists _ = Right False

checkSchemeInduction :: Expr -> Bool
checkSchemeInduction (Impl (And phi0 (Forall x (Impl phi phi'))) phi'') =
  phi'' == phi &&
  case (findSubstitution x phi phi0, findSubstitution x phi phi') of
    (Just (Just Zero), Just (Just (Succ (TermVar x')))) -> x == x'
    _ -> False
checkSchemeInduction _ = False

checkAxiom :: Int -> Expr -> Maybe AnnotatedExpr
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
    (a:_) -> Just $ AnnotatedExpr e $ ArithmeticAxiom n $ ArithmeticNumber a
    [] -> Nothing
  where
    applyAxiom e (n, ax) = if ax e then Just n else Nothing

axiom1 (Impl (ExprPred (PredEq (TermVar a) (TermVar b))) (Impl (ExprPred (PredEq (TermVar a') (TermVar c))) (ExprPred (PredEq (TermVar b') (TermVar c'))))) =
  a == a' && b == b' && c == c'
axiom1 _ = False
axiom2 (Impl (ExprPred (PredEq (TermVar a) (TermVar b))) (ExprPred (PredEq (Succ (TermVar a')) (Succ (TermVar b'))))) =
  a == a' && b == b'
axiom2 _ = False
axiom3 (Impl (ExprPred (PredEq (Succ (TermVar a)) (Succ (TermVar b)))) (ExprPred (PredEq (TermVar a') (TermVar b')))) =
  a == a' && b == b'
axiom3 _ = False
axiom4 (Not (ExprPred (PredEq (Succ (TermVar a)) Zero))) = True
axiom4 _ = False
axiom5 (ExprPred (PredEq (Plus (TermVar a) Zero) (TermVar a'))) =
  a == a'
axiom5 _ = False
axiom6 (ExprPred (PredEq (Plus (TermVar a) (Succ (TermVar b))) (Succ (Plus (TermVar a') (TermVar b'))))) =
  a == a' && b == b'
axiom6 _ = False
axiom7 (ExprPred (PredEq (Times (TermVar a) Zero) Zero)) = True
axiom7 _ = False
axiom8 (ExprPred (PredEq (Times (TermVar a) (Succ (TermVar b))) (Plus (Times (TermVar a') (TermVar b')) (TermVar a'')))) =
  a == a' && a' == a'' && b == b'
axiom8 _ = False

checkRules :: Int -> [Expr] -> Expr -> Either AnnotationError (Maybe AnnotatedExpr)
checkRules n es e =
  case checkModusPonens n es e of
    ae@(Just _) -> Right ae
    Nothing ->
      case checkExistsRule n es e of
        err@(Left _) -> err
        a@(Right (Just _)) -> a
        Right Nothing ->
          case checkForallRule n es e of
            err@(Left _) -> err
            a@(Right (Just _)) -> a
            Right Nothing -> Right Nothing
            

checkModusPonens :: Int -> [Expr] -> Expr -> Maybe AnnotatedExpr
checkModusPonens n es e =
  case mapMaybe (check e) [(i, j) | i <- zip [1..] es, j <- zip [1..] es] of
    ((k, l):_) -> Just $ AnnotatedExpr e $ ModusPonens n k l
    [] -> Nothing
  where
    check e ((k, e1), (l, Impl e1' e')) = if e1' == e1 && e == e' then Just (k, l) else Nothing
    check _ _ = Nothing

checkExistsRule :: Int -> [Expr] -> Expr -> Either AnnotationError (Maybe AnnotatedExpr)
checkExistsRule n es e =
  case mapMaybe (check e) $ zip [1..] es of
    ((Left e):_) -> Left $ NonFreeExists n e
    ((Right k):_) -> Right $ Just (AnnotatedExpr e $ ExistsRule n k)
    [] -> Right Nothing
  where
    check :: Expr -> (Int, Expr) -> Maybe (Either Var Int)
    check (Impl (Exists x phi) psi) (k, Impl phi' psi') =
      if phi == phi' && psi == psi'
      then if hasFree x phi
              then Just $ Right k
              else Just $ Left x
      else Nothing
    check _ _ = Nothing

checkForallRule :: Int -> [Expr] -> Expr -> Either AnnotationError (Maybe AnnotatedExpr)
checkForallRule n es e =
  case mapMaybe (check e) $ zip [1..] es of
    ((Left e):_) -> Left $ NonFreeForall n e
    ((Right k):_) -> Right $ Just (AnnotatedExpr e $ ForallRule n k)
    [] -> Right Nothing
  where
    check :: Expr -> (Int, Expr) -> Maybe (Either Var Int)
    check (Impl phi (Forall x psi)) (k, Impl phi' psi') =
      if phi == phi' && psi == psi'
      then if hasFree x phi
              then Just $ Right k
              else Just $ Left x
      else Nothing
    check _ _ = Nothing
