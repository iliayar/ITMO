module HW1.T6
    ( mcat
    , epart
    ) where

import Data.Maybe (fromMaybe)

mcat :: Monoid a => [Maybe a] -> a
mcat = foldl (\acc e -> acc <> fromMaybe mempty e) mempty

epart :: (Monoid a, Monoid b) => [Either a b] -> (a, b)
epart = foldl add (mempty, mempty)
  where
    add :: (Monoid a, Monoid b) => (a, b) -> Either a b -> (a, b)
    add (a, b) (Left l)  = (a <> l, b)
    add (a, b) (Right r) = (a, b <> r)
