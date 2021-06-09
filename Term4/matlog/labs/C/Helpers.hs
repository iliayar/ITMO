module Helpers where

import qualified Data.Map as M
import Control.Applicative ((<|>))


braced :: String -> String
braced s = "(" ++ s ++ ")"


findMin :: Ord k => M.Map k a -> Maybe (k, a)
findMin m = if M.null m then Nothing else Just $ M.findMin m


(<?>) :: Either a (Maybe b) -> Either a (Maybe b) -> Either a (Maybe b)
Left l <?> Left r = Left r
Left l <?> Right r@(Just _)  = Right r
Left l <?> Right Nothing = Left l
Right l@(Just _) <?> Left r = Right l
Right Nothing <?> Left r = Left r
Right l <?> Right r = Right $ l <|> r

