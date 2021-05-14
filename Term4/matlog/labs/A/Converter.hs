module Converter where

import qualified ProofChecker as PC
import qualified Proof as P
import Natural

import Data.List (last)

convert :: [P.Expression] -> P.Expression -> [(PC.Reason, P.Expression)] -> Node
convert = convert' [] []

convert' :: [(Statement -> Node)] -> [P.Expression] -> [P.Expression] -> P.Expression -> [(PC.Reason, P.Expression)] -> Node
convert' nodes es hypos st ((r, e):ls) = convert'
    (nodes ++ 
    [ case r of
        (PC.Axiom i) -> axioms !! i
        (PC.ModusPonens i j) -> makeImplDel (convertExpression $ es !! i) (nodes !! j) (nodes !! i)
        PC.Hypo -> makeAxiom ]) (es ++ [e]) hypos st ls
convert' nodes es hypos st [] = last nodes (map convertExpression hypos, convertExpression st)

