module HW1.T4
    ( tfoldr
    ) where

import HW1.T3

tfoldr :: (a -> b -> b) -> b -> Tree a -> b
tfoldr f initValue (Branch _ left a right) =
  let rightValue = tfoldr f initValue right
      curValue = f a rightValue
   in tfoldr f curValue left
tfoldr _ initValue Leaf = initValue
