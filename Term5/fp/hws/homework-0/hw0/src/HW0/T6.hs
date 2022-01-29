module HW0.T6 where

import Data.Char (isSpace)
import HW0.T1 (distrib)

a = distrib (Left ("AB" ++ "CD" ++ "EF"))

b = map isSpace "Hello, World"

c = if 1 > 0 || error "X" then "Y" else "Z"

-- `distrib` application -> `(,)` constructor
a_whnf = (Left ("AB" ++ "CD" ++ "EF"), Left ("AB" ++ "CD" ++ "EF"))

-- Assume map is defined as:
-- map f [x:xs] = f x : map f xs
-- map _ [] = []
-- `map isSpace` application -> `:` constructor
b_whnf = (isSpace 'H'):(map isSpace "ello, World")

-- `1 > 0` === true -> `1 > 0 || error "X"` === true -> `if true then "Y" else "Z"` === "Y"
c_whnf = "Y"
