module HW0.T4 where

import Data.Function (fix)
import Numeric.Natural (Natural)

repeat' :: a -> [a]
repeat' x = fix (x :)

map' :: (a -> b) -> [a] -> [b]
map' f = fix g
  where
    g fb [] = []
    g fb (a : as) = f a : fb as

fib :: Natural -> Natural
fib = fix g 0 1
  where
    g fn f1 f2 0 = f1
    g fn f1 f2 n = fn f2 (f1 + f2) (n - 1)

fac :: Natural -> Natural
fac = fix g 1
  where
    g fn f 0 = f
    g fn f n = fn (f * n) (n - 1)
