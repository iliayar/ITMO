module Helpers where

import qualified Data.Map as M
import Control.Applicative ((<|>))


braced :: String -> String
braced s = "(" ++ s ++ ")"


findMin :: (Ord a) => M.Map k a -> Maybe (k, a)
findMin m = case  M.toList m of
              lst@(_:_) -> Just $ foldr1 (\ (kl, l) (kr, r) -> if l < r then (kl, l) else (kr, r)) lst
              [] -> Nothing


(<?>) :: Either a (Maybe b) -> Either a (Maybe b) -> Either a (Maybe b)
Left l <?> Left r = Left r
Left l <?> Right r@(Just _)  = Right r
Left l <?> Right Nothing = Left l
Right l@(Just _) <?> Left r = Right l
Right Nothing <?> Left r = Left r
Right l <?> Right r = Right $ l <|> r

