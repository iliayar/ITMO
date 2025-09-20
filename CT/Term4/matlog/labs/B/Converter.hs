module Converter where

import qualified ProofChecker as PC
import qualified Proof as P
import qualified Data.Map as M
import Natural

import Data.List (last)

convert :: [P.Expression] -> P.Expression -> [(PC.Reason, P.Expression)] -> Node
convert = convert' M.empty M.empty

convert' :: M.Map Int (Statement -> Node) -> M.Map Int P.Expression -> [P.Expression] -> P.Expression -> [(PC.Reason, P.Expression)] -> Node
convert' nodes es hypos st ((r, e):ls) = convert'
    (M.insert (M.size nodes)
    (case r of
        (PC.Axiom i) -> axioms !! i
        (PC.ModusPonens i j) ->
          let Just ei = M.lookup i es
              Just nj = M.lookup j nodes
              Just ni = M.lookup i nodes
          in makeImplDel (convertExpression $ ei) nj ni
        PC.Hypo -> makeAxiom) nodes) (M.insert (M.size es) e es) hypos st ls
convert' nodes es hypos st [] = (snd $ M.findMax nodes) (map convertExpression hypos, convertExpression st)

