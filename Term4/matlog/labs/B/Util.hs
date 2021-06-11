module Util where

import qualified Data.Map as M

findJust :: (a -> Maybe b) -> [a] -> Maybe b
findJust predicate (a:as) = 
    case predicate a of
        (Just value) -> Just value
        _ -> findJust predicate as
findJust _ [] = Nothing

findMin :: (Ord a) => M.Map k a -> Maybe (k, a)
findMin m = case  M.toList m of
              lst@(_:_) -> Just $ foldr1 (\ (kl, l) (kr, r) -> if l < r then (kl, l) else (kr, r)) lst
              [] -> Nothing
