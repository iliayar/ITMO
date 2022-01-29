module HW1.T5
    ( splitOn
    , joinWith
    ) where

import Data.List.NonEmpty (NonEmpty ((:|)))

splitOn :: Eq a => a -> [a] -> NonEmpty [a]
splitOn sep lst = let (res, cur) = splitOn' lst in cur :| res
  where
    splitOn' [] = ([], [])
    splitOn' (x : xs) =
      let (res, cur) = splitOn' xs
       in if x == sep
            then (cur : res, [])
            else (res, x : cur)

joinWith :: a -> NonEmpty [a] -> [a]
joinWith sep (first :| lst) = first ++ joinWith' lst
  where
    joinWith' []       = []
    joinWith' (x : xs) = sep : x ++ joinWith' xs
