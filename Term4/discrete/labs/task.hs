import Control.Monad
import Data.List

modulus = 998244353

data GenFunc = Polynom [Rational] 
              | Mult GenFunc GenFunc 
              | Sum GenFunc GenFunc 
              | Div GenFunc GenFunc
              | Subst GenFunc GenFunc
    deriving (Show)

class Gen a where
    getAll :: a -> [Rational]
    getFirstN :: Int -> a -> [Rational]
    getFirstN n = (take n) . getAll

paddZeros = (++(repeat 0))
take' n = (take n) . paddZeros

instance Gen GenFunc where
    getAll (Polynom p) = paddZeros $ p
    getAll (Sum g1 g2) = zipWith (+) (getAll $ g1) (getAll $ g2)
    getAll (Mult g1 g2) = 
        let p1 = getAll g1
            p2 = getAll g2
        in [getN (take n p1) (take n p2) | n <- [1..]]
        where
            getN p1 p2 = sum $ zipWith (*) p1 (reverse p2)
    getAll (Div g1 g2) =
        let (x:p1) = getAll g1
            (y:p2) = getAll g2
            c0 = (x / y)
        in c0 : (getAll' p1 (y:p2) [c0] 1)
        where
            getAll' (x:p1) (z:p2) (y:c) n = 
                let cn = ((x - (sum $ zipWith (*) (reverse $ take n (p2)) (take n (y:c)))) / z)
                in cn : (getAll' p1 (z:p2) ((y:c) ++ [cn]) $ n + 1)
      

readInt :: String -> Int
readInt = read

showInt :: Int -> String
showInt = show


getElements :: [Int] -> [Int] -> [Int]
getElements a = getElements' (length a) a
getElements' :: Int -> [Int] -> [Int] -> [Int]
getElements' _ _ [] = []
getElements' 0 [] _ = []
getElements' _ [] _ = undefined
getElements' i (a:as) (id:ids) = if id == i then a : getElements' i (a:as) ids else getElements' (i - 1) as (id:ids)

test :: [Int] -> Int -> Int -> Int -> [Int] -> Int
test b pk 0 0 ks = foldl (*) 1 $ getElements b ks
test b pk n 1 ks = test b pk 0 0 (n : ks)
test b pk n i ks = foldl (+) 0 $ [test b k (n - k) (i - 1) (k : ks) | k <- [pk..(n `div` i)]]

main = do
  putStrLn $ show $ test [0..10] 0 10 3 []
  -- putStrLn $ show $ getElements [1, 2, 3] [0, 1, 2] 
  return ()
