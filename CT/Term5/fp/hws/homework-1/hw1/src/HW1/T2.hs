module HW1.T2
    ( N (..)
    , nplus
    , nmult
    , nsub
    , ncmp
    , nFromNatural
    , nToNum
    , nEven
    , nOdd
    , ndiv
    , nmod
    ) where

import Data.Maybe (fromJust)
import Numeric.Natural (Natural)

data N = Z | S N

nplus :: N -> N -> N
nplus Z     = id
nplus (S n) = S . nplus n

nmult :: N -> N -> N
nmult Z     = const Z
nmult (S n) = nplus <*> nmult n

nsub :: N -> N -> Maybe N
nsub Z (S _)     = Nothing
nsub n Z         = Just n
nsub (S a) (S b) = nsub a b

ncmp :: N -> N -> Ordering
ncmp n = maybe LT ncmp' . nsub n
  where
    ncmp' :: N -> Ordering
    ncmp' Z = EQ
    ncmp' _ = GT

nFromNatural :: Natural -> N
nFromNatural 0 = Z
nFromNatural n = S $ nFromNatural $ n - 1

nToNum :: Num a => N -> a
nToNum Z     = 0
nToNum (S n) = 1 + nToNum n

nEven, nOdd :: N -> Bool
nEven = (== EQ) . ncmp Z . (`nmod` S (S Z))
nOdd = not . nEven

ndivmod :: N -> N -> (N, N)
ndivmod a b =
  case ncmp a b of
    LT -> (a, Z)
    EQ -> (Z, S Z)
    GT -> incSnd $ ndivmod (fromJust $ nsub a b) b
  where
    incSnd (m, d) = (m, nplus d (S Z))

ndiv :: N -> N -> N
ndiv a = snd . ndivmod a

nmod :: N -> N -> N
nmod a = fst . ndivmod a
