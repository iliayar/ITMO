module HW2.T2
  ( distOption
  , distPair
  , distQuad
  , distAnnotated
  , distExcept
  , distPrioritised
  , distStream
  , distList
  , distFun
  , wrapOption
  , wrapPair
  , wrapQuad
  , wrapAnnotated
  , wrapExcept
  , wrapPrioritised
  , wrapStream
  , wrapList
  , wrapFun ) where

import HW2.T1
import Prelude (Monoid, Semigroup, mempty, (<>))

-- |Make a pair of elements only if both are present
distOption :: (Option a, Option b) -> Option (a, b)
distOption (None, _)        = None
distOption (_, None)        = None
distOption (Some a, Some b) = Some (a, b)

-- |Make a pair of provided pairs
distPair :: (Pair a, Pair b) -> Pair (a, b)
distPair (P a b, P c d) = P (a, c) (b, d)

-- |Make a pair of two four element tuples
distQuad :: (Quad a, Quad b) -> Quad (a, b)
distQuad (Q a b c d, Q w x y z) = Q (a, w) (b, x) (c, y) (d, z)

-- |Make a pair of values, concatinating the addtitional information
-- of each one
distAnnotated :: Semigroup e => (Annotated e a, Annotated e b) -> Annotated e (a, b)
distAnnotated (a :# eLeft, b :# eRight) = (a, b) :# eRight <> eLeft

-- |Make a pair of values, only if both are not error
distExcept :: (Except e a, Except e b) -> Except e (a, b)
distExcept (Error e, _)           = Error e
distExcept (_, Error e)           = Error e
distExcept (Success a, Success b) = Success (a, b)

-- |Make a pair of values with new priority equals the highest one
distPrioritised :: (Prioritised a, Prioritised b) -> Prioritised (a, b)
distPrioritised p =
  case p of
    (High a, b)   -> High (a, get b)
    (a, High b)   -> High (get a, b)
    (Medium a, b) -> Medium (a, get b)
    (a, Medium b) -> Medium (get a, b)
    (a, b)        -> Low (get a, get b)
  where
    get :: Prioritised a -> a
    get (High a)   = a
    get (Medium a) = a
    get (Low a)    = a

-- |Make a stream of pairs of values, taking one from first and second stream
distStream :: (Stream a, Stream b) -> Stream (a, b)
distStream (a :> as, b :> bs) = (a, b) :> distStream (as, bs)

-- |Make a list of pairs, for each element in the first list and each
-- one in the second list
distList :: (List a, List b) -> List (a, b)
distList = distList' Nil
  where
    mkPairs' :: List (a, b) -> a -> List b -> List (a, b)
    mkPairs' r _ Nil       = r
    mkPairs' r a (b :. bs) = (a, b) :. mkPairs' r a bs

    distList' :: List (a, b) -> (List a, List b) -> List (a, b)
    distList' r (Nil, _)      = r
    distList' r (a :. as, bs) =  mkPairs' (distList' r (as, bs)) a bs

-- |Make a function, that returns pair using two provided functions
distFun :: (Fun i a, Fun i b) -> Fun i (a, b)
distFun (F f, F g) = F (\i -> (f i, g i))

-- |Make an Option object with provided value inside
wrapOption :: a -> Option a
wrapOption = Some

-- |Make a pair from provided values copies it
wrapPair :: a -> Pair a
wrapPair a = P a a

-- |Make a tuple of four from provided values copies it
wrapQuad :: a -> Quad a
wrapQuad a = Q a a a a

-- |Make an annotated object from provide value and no additional data
wrapAnnotated :: Monoid e => a -> Annotated e a
wrapAnnotated = (:# mempty)

-- |Make an success computation result from provided value
wrapExcept :: a -> Except e a
wrapExcept = Success

-- |Make a values with lowest priority
wrapPrioritised :: a -> Prioritised a
wrapPrioritised = Low

-- |Make an infinit stream repeating provided value
wrapStream :: a -> Stream a
wrapStream a = a :> wrapStream a

-- |Make a list of one element provided
wrapList :: a -> List a
wrapList a = a :. Nil

-- |Make a function, that ignores its argument and returns provided
-- value
wrapFun :: a -> Fun i a
wrapFun a = F (\_ -> a)
