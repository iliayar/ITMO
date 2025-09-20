module HW1.T7
    ( ListPlus (..)
    , Inclusive (..)
    , DotString (..)
    , Fun (..)
    ) where

data ListPlus a = a :+ ListPlus a | Last a

infixr 5 :+

instance Semigroup (ListPlus a) where
  Last x <> right    = x :+ right
  (x :+ xs) <> right = x :+ (xs <> right)

data Inclusive a b = This a | That b | Both a b

instance (Semigroup a, Semigroup b) => Semigroup (Inclusive a b) where
  (Both al bl) <> r = uncurry Both $
    case r of
      (This ar)    -> (al <> ar, bl)
      (That br)    -> (al, bl <> br)
      (Both ar br) -> (al <> ar, bl <> br)
  l <> (Both ar br) = uncurry Both $
    case l of
      (This al)    -> (al <> ar, br)
      (That bl)    -> (ar, bl <> br)
      (Both al bl) -> (al <> ar, bl <> br)
  (This al) <> (This ar) = This (al <> ar)
  (This al) <> (That br) = Both al br
  (That bl) <> (That br) = That (bl <> br)
  (That bl) <> (This ar) = Both ar bl

newtype DotString = DS String

instance Semigroup DotString where
  DS l <> DS [] = DS l
  DS [] <> DS r = DS r
  DS l <> DS r  = DS $ l ++ "." ++ r

instance Monoid DotString where
  mempty = DS []

newtype Fun a = F (a -> a)

instance Semigroup (Fun a) where
  (F f) <> (F g) = F $ f . g

instance Monoid (Fun a) where
  mempty = F id
