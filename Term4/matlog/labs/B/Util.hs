module Util where

import qualified Data.Map as M

findJust :: (a -> Maybe b) -> [a] -> Maybe b
findJust predicate (a:as) = 
    case predicate a of
        (Just value) -> Just value
        _ -> findJust predicate as
findJust _ [] = Nothing

findMin :: (Ord a) => M.Map k a -> Maybe (k, a)
findMin m = if M.null m then Nothing else Just $ M.elemAt 0 m
