module Natural where

import Proof

type Prerequest = ([Expression], Expression)

data Natural = 
    Axiom Prerequest
    | ImplAdd Prerequest Natural | ImplDel Prerequest Natural Natural
    | AndAdd Prerequest Natural Natural | AndDelLeft Prerequest Natural | AndDelRight Prerequest Natural
    | OrAddLeft Prerequest Natural | OrAddRight Prerequest Natural | OrDel Prerequest Natural Natural Natural
    | FalseDel Prerequest Natural

naturalAxioms :: [Expression -> Natural]
naturalAxioms = 
    [ (\(Impl alpha (Impl beta alpha')) ->
        ImplAdd ([], (Impl alpha (Impl beta alpha))) $
            ImplAdd ([alpha], (Impl beta alpha)) $
                Axiom ([alpha, beta], alpha)) ]
