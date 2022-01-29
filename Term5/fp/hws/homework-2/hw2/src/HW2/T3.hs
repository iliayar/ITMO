module HW2.T3
  ( joinOption
  , joinExcept
  , joinAnnotated
  , joinList
  , joinFun ) where

import HW2.T1 (Annotated (..), Except (..), Fun (..), List (..), Option (..))

-- |Flatten an optional value. Value is present only if the inner and
-- outer value is presented
joinOption :: Option (Option a) -> Option a
joinOption None            = None
joinOption (Some None)     = None
joinOption (Some (Some a)) = Some a

-- |Flatten a posible computation failure value. The is not an error
-- only if onner and outer results are not failure
joinExcept :: Except e (Except e a) -> Except e a
joinExcept (Error e)             = Error e
joinExcept (Success (Error e))   = Error e
joinExcept (Success (Success a)) = Success a

-- |Flatten two annotated values. The result value is one in inner
-- object. The additional data of result is concatenation of outer and
-- inner additional data.
joinAnnotated :: Semigroup e => Annotated e (Annotated e a) -> Annotated e a
joinAnnotated ((a :# eFirst) :# eSecond) = a :# eFirst <> eSecond

-- |Concatened all lists in outer list.
joinList :: List (List a) -> List a
joinList Nil               = Nil
joinList (Nil :. ls)       = joinList ls
joinList ((a :. as) :. ls) = a :. joinList (as :. ls)

-- |Make a function that apllies its argument twice to provided
-- function
joinFun :: Fun i (Fun i a) -> Fun i a
joinFun (F f) = F $ \i -> case f i of F g -> g i
