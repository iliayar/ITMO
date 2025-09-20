module HW2.T1
  ( Option(..)
  , Pair(..)
  , Quad(..)
  , Annotated(..)
  , Except(..)
  , Prioritised(..)
  , Stream(..)
  , List(..)
  , Fun(..)
  , Tree(..)
  , mapOption
  , mapPair
  , mapQuad
  , mapAnnotated
  , mapExcept
  , mapPrioritised
  , mapStream
  , mapList
  , mapFun
  , mapTree ) where

import Prelude ()

-- |Data type represents posibility for absent value
data Option a
  = None -- ^ No value
  | Some a -- ^ Value presented

-- |Data type combine two values of same type
data Pair a = P a a

-- |Data type combine four values of same type
data Quad a = Q a a a a

-- |Data type represents value with additional inforamtion
data Annotated e a = a :# e

infix 0 :#

-- |Data type represents posibility of computation failure
data Except e a
  = Error e -- ^ Error occured
  | Success a -- ^ Not error, value presented

-- |Data type with support of different priority for valuu
data Prioritised a = Low a | Medium a | High a

-- |Data type of infinite sequence of elements of the same type
data Stream a = a :> Stream a

infixr 5 :>

-- |List data type
data List a
  = Nil -- ^ Empty list
  | a :. List a -- ^ One element and the rest of the list

infixr 5 :.

-- |Data type wrapper for function
data Fun i a = F (i -> a)

-- |Data type of binary tree with value in each node
data Tree a
  = Leaf -- ^ Empty tree
  | Branch (Tree a) a (Tree a)  -- ^ Node of the tree

-- |Apply a function to element if it presents
mapOption :: (a -> b) -> (Option a -> Option b)
mapOption _ None     = None
mapOption f (Some a) = Some (f a)

-- |Apply a function to both elements in Pair
mapPair :: (a -> b) -> (Pair a -> Pair b)
mapPair f (P a b) = P (f a) (f b)

-- |Apply a function to all four elements
mapQuad :: (a -> b) -> (Quad a -> Quad b)
mapQuad f (Q a b c d) = Q (f a) (f b) (f c) (f d)

-- |Apply a function to a value, keeping additional information
mapAnnotated :: (a -> b) -> (Annotated e a -> Annotated e b)
mapAnnotated f (a :# e) = f a :# e

-- |Apply a function to a value, if there is no error
mapExcept :: (a -> b) -> (Except e a -> Except e b)
mapExcept _ (Error e)   = Error e
mapExcept f (Success a) = Success (f a)

-- |Apply a function to value, not depending on its priority
mapPrioritised :: (a -> b) -> (Prioritised a -> Prioritised b)
mapPrioritised f (Low a)    = Low (f a)
mapPrioritised f (Medium a) = Medium (f a)
mapPrioritised f (High a)   = High (f a)

mapStream :: (a -> b) -> (Stream a -> Stream b)
mapStream f (a :> as) = f a :> mapStream f as

-- |Apply a function to each element in the list
mapList :: (a -> b) -> (List a -> List b)
mapList _ Nil       = Nil
mapList f (a :. as) = f a :. mapList f as

-- |Apply a function to return value of provided function
mapFun :: (a -> b) -> (Fun i a -> Fun i b)
mapFun f (F g) = F (\x -> f (g x))

-- |Apply a function to each node's element in the tree
mapTree :: (a -> b) -> (Tree a -> Tree b)
mapTree _ Leaf                  = Leaf
mapTree f (Branch left a right) = Branch (mapTree f left) (f a) (mapTree f right)
