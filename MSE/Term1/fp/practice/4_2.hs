f :: Int -> a -> a
f = undefined

g :: Int -> Double
g = undefined

h :: Int -> Double -> Int
h = undefined

p x = f 1 (g (h 2 x))
p' x = f 1 $ g $ h 2 x
p'' = f 1 . g . h 2

