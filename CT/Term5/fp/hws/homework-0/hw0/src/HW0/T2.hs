module HW0.T2 where

import Data.Void (Void)

type Not a = a -> Void

doubleNeg :: a -> Not (Not a)
doubleNeg = flip ($)

reduceTripleNeg :: Not (Not (Not a)) -> Not a
reduceTripleNeg = (. doubleNeg)
