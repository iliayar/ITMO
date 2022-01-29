module HW0.T5 where

import Numeric.Natural (Natural)

type Nat a = (a -> a) -> a -> a

nz :: Nat a
nz _ = id

ns :: Nat a -> Nat a
ns n f x = f (n f x)

nplus, nmult :: Nat a -> Nat a -> Nat a
nplus a b f x = a f (b f x)
nmult a b f = a (b f)

nFromNatural :: Natural -> Nat a
nFromNatural 0 = nz
nFromNatural n = ns $ nFromNatural $ n - 1

nToNum :: Num a => Nat a -> a
nToNum a = a (+1) 0
