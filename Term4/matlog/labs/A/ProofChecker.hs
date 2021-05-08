module ProofChecker (axiom) where

import Proof

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
    -- FIXME: 9, 10 axiom ???
    , \e -> case e of
        (Impl (Impl alpha beta) (Impl (Impl alpha' (Not beta')) (Not alpha''))) ->
            alpha == alpha' && alpha' == alpha'' && beta == beta'
        _ -> False
    , \e -> case e of
        (Impl (Not (Not alpha)) alpha') ->
            alpha == alpha'
        _ -> False ]

