module ProofChecker (checkProof) where

import Proof
import Util

data Reason = Axiom Int | ModusPonens Int Int | Hypo
    deriving (Show)

checkProof :: [Expression] -> [Expression] -> Expression -> [(Maybe Reason, Expression)]
checkProof = checkProof' []

checkProof' :: [Expression] -> [Expression] -> [Expression] -> Expression -> [(Maybe Reason, Expression)]
checkProof' was hypos (e:es) res = (checkStatement was hypos e, e) : (checkProof' (was ++ [e]) hypos es res)
    where 
        checkStatement was hypos e = 
            case checkAxiom e of
                (Just r) -> (Just r)
                _ -> case checkMP was was e of
                    (Just r) -> (Just r)
                    _ -> if e `elem` hypos then Just Hypo else Nothing
        checkAxiom e = findJust (\(a, i) -> if a e then Just $ Axiom i else Nothing) $ zip axioms [1..]
        checkMP was wasTmp e = findJust (\e1 -> checkMP' was e1 e) $ zip wasTmp [1..]
        checkMP' was (cur, i) e = findJust (\e1 -> checkMP'' e1 (cur, i) e) $ zip was [1..]
        checkMP'' (ek, k) (el, l) e = 
            case ek of
                (Impl e1 e2) -> 
                    if e1 == el && e2 == e
                    then Just $ ModusPonens l k
                    else Nothing
                _ -> Nothing
checkProof' _ _ _ _ = []

axiom :: Expression -> Bool
axiom e = any (\a -> a e) axioms

axioms :: [Expression -> Bool]
axioms = 
    [ \e -> case e of
        (Impl alpha (Impl beta alpha')) ->
            alpha == alpha'
        _ -> False
    , \e -> case e of
        (Impl (Impl alpha beta) (Impl (Impl alpha' (Impl beta' gamma)) (Impl alpha'' gamma'))) ->
            alpha == alpha' && alpha' == alpha'' && beta == beta' && gamma == gamma'
        _ -> False
    , \e -> case e of
        (Impl alpha (Impl beta (And alpha' beta'))) ->
            alpha == alpha' && beta == beta'
        _ -> False
    , \e -> case e of
        (Impl (And alpha beta) alpha') ->
            alpha == alpha'
        _ -> False
    , \e -> case e of
        (Impl (And alpha beta) beta') ->
            beta == beta'
        _ -> False
    , \e -> case e of
        (Impl alpha (Or alpha' beta)) ->
            alpha == alpha'
        _ -> False
    , \e -> case e of
        (Impl beta (Or alpha beta')) ->
            beta == beta'
        _ -> False
    , \e -> case e of
        (Impl (Impl alpha gamma) (Impl (Impl beta gamma') (Impl (Or alpha' beta') gamma''))) ->
            alpha == alpha' && beta == beta' && gamma == gamma' && gamma' == gamma''
        _ -> False
    , \e -> case e of
        (Impl (Impl alpha beta) (Impl (Impl alpha' (Not beta')) (Not alpha''))) ->
            alpha == alpha' && alpha' == alpha'' && beta == beta'
        _ -> False
    , \e -> case e of
        (Impl alpha (Impl (Not alpha') beta)) ->
            alpha == alpha'
        _ -> False ]

