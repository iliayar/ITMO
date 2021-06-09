module Helpers where

import qualified Data.Map as M

braced :: String -> String
braced s = "(" ++ s ++ ")"


findMin :: Ord k => M.Map k a -> Maybe (k, a)
findMin m = if M.null m then Nothing else Just $ M.findMin m
