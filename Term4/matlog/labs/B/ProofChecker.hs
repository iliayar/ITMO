module ProofChecker where

import Proof
import Util
import Data.Maybe (isJust)
import qualified Data.Map as M

data Reason = Axiom Int | ModusPonens Int Int | Hypo
    deriving (Show)

data ProofError = Line Int | Whole | Ok

findError :: [(Maybe Reason, Expression)] -> Expression -> ProofError
findError lines res = case findError' 1 lines of
                    r@(Line _) -> r
                    _ -> let (_, e) = last lines
                            in if e /= res
                                then Whole else Ok
    where
        findError' n ((Just r, e):ls) = findError' (n + 1) ls
        findError' n ((Nothing, r):ls) = Line n
        findError' _ [] = Ok

checkProof :: [Expression] -> [Expression] -> [(Maybe Reason, Expression)]
checkProof = checkProof' 0 M.empty

catProofMaybes :: [(Maybe Reason, Expression)] -> [(Reason, Expression)]
catProofMaybes [] = []
catProofMaybes ((Just r, e):ls) = (r, e):catProofMaybes ls

checkProof' :: Int -> M.Map Expression Int -> [Expression] -> [Expression] -> [(Maybe Reason, Expression)]
checkProof' n was hypos (e:es) = (checkStatement was hypos e, e) : checkProof' (n + 1) (M.insert e n was) hypos es
    where
        checkStatement was hypos e =
            case checkAxiom e of
                (Just r) -> Just r
                _ -> case checkMP was e of
                    (Just r) -> Just r
                    _ -> if e `elem` hypos then Just Hypo else Nothing
        checkAxiom e = findJust (\(a, i) -> if a e then Just $ Axiom i else Nothing) $ zip axioms [0..]
        checkMP es e =
          let es' = M.mapMaybeWithKey (checkMP' e es) es
          in case findMin es' of
            Just (_, (k, l)) -> Just $ ModusPonens k l
            Nothing -> Nothing
        checkMP' e es (Impl e1 e') l =
          if e == e'
          then case M.lookup e1 es of
            Just k -> Just (k, l)
            Nothing -> Nothing
          else Nothing
        checkMP' _ _ _ _ = Nothing
checkProof' _ _ _ _ = []

axiom :: Expression -> Bool
axiom e = any (\a -> a e) axioms

axioms :: [Expression -> Bool]
axioms =
    [ isJust . matchAxiom1
    , isJust . matchAxiom2
    , isJust . matchAxiom3
    , isJust . matchAxiom4
    , isJust . matchAxiom5
    , isJust . matchAxiom6
    , isJust . matchAxiom7
    , isJust . matchAxiom8
    , isJust . matchAxiom9
    , isJust . matchAxiom10 ]

matchAxiom1 (Impl alpha (Impl beta alpha'))
    | alpha == alpha' = Just (alpha, beta)
    | otherwise = Nothing
matchAxiom1 _ = Nothing
matchAxiom2 (Impl (Impl alpha beta) (Impl (Impl alpha' (Impl beta' gamma)) (Impl alpha'' gamma')))
    | alpha == alpha' && alpha' == alpha'' && beta == beta' && gamma == gamma' = Just (alpha, beta, gamma)
    | otherwise = Nothing
matchAxiom2 _ = Nothing
matchAxiom3 (Impl alpha (Impl beta (And alpha' beta')))
    | alpha == alpha' && beta == beta' = Just (alpha, beta)
    | otherwise = Nothing
matchAxiom3 _ = Nothing
matchAxiom4 (Impl (And alpha beta) alpha')
    | alpha == alpha' = Just (alpha, beta)
    | otherwise = Nothing
matchAxiom4 _ = Nothing
matchAxiom5 (Impl (And alpha beta) beta')
    | beta == beta' = Just (alpha, beta)
    | otherwise = Nothing
matchAxiom5 _ = Nothing
matchAxiom6 (Impl alpha (Or alpha' beta))
    | alpha == alpha' = Just (alpha, beta)
    | otherwise = Nothing
matchAxiom6 _ = Nothing
matchAxiom7 (Impl beta (Or alpha beta'))
    | beta == beta' = Just (alpha, beta)
    | otherwise = Nothing
matchAxiom7 _ = Nothing
matchAxiom8 (Impl (Impl alpha gamma) (Impl (Impl beta gamma') (Impl (Or alpha' beta') gamma'')))
    | alpha == alpha' && beta == beta' && gamma == gamma' && gamma' == gamma'' = Just (alpha, beta, gamma)
    | otherwise = Nothing
matchAxiom8 _ = Nothing
matchAxiom9 (Impl (Impl alpha beta) (Impl (Impl alpha' (Not beta')) (Not alpha'')))
    | alpha == alpha' && alpha' == alpha'' && beta == beta' = Just (alpha, beta)
    | otherwise = Nothing
matchAxiom9 _ = Nothing
matchAxiom10 (Impl alpha (Impl (Not alpha') beta))
    | alpha == alpha' = Just (alpha, beta)
    | otherwise = Nothing
matchAxiom10 _ = Nothing
