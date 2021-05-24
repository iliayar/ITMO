module Util where

findJust :: (a -> Maybe b) -> [a] -> Maybe b
findJust predicate (a:as) = 
    case predicate a of
        (Just value) -> Just value
        _ -> findJust predicate as
findJust _ [] = Nothing
