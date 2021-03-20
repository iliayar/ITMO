import Control.Monad
import Data.List
import Data.Ratio (numerator, denominator, (%))
import Data.Maybe (fromJust)

modulus :: Int
modulus = 998244353

data GenFunc = Polynom [Rational] 
              | Mult GenFunc GenFunc 
              | Sum GenFunc GenFunc 
              | Div GenFunc GenFunc
              | Subst GenFunc GenFunc -- Subst A(t) B(t) == A(B(t))
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
    getAll (Subst g1 g2) =
      let (a:as) = getAll g1
          bs = getAll g2
      in a : [getN n as bs | n <- [1..]]
      where
        getN n as bs = sum $ zipWith (*) as $ map (\i -> sumProds n i bs) [1..n] 
      

readInt :: String -> Int
readInt = read

showInt :: Int -> String
showInt = show

factorial :: Int -> Int
factorial n = foldl (*) 1 [1..n]
comb n k = (factorial n) `div` ((factorial k) * (factorial $ n - k))

getElements :: [Rational] -> [Int] -> [Rational]
getElements a = getElements' 0 a
getElements' :: Int -> [Rational] -> [Int] -> [Rational]
getElements' _ _ [] = []
getElements' _ [] _ = undefined
getElements' i (a:as) (id:ids) = if id == i then a : getElements' i (a:as) ids else getElements' (i + 1) as (id:ids)

sumProds = sumProds' []
sumProds' :: [Int] -> Int -> Int -> [Rational] -> Rational
sumProds' ks 0 0 b = foldl (*) 1 $ getElements b $ sort ks
sumProds' ks n 1 b = sumProds' (n : ks) 0 0 b
sumProds' ks n i b = foldl (+) 0 $ [sumProds' (k : ks) (n - k) (i - 1) b | k <- [0..n]]

-- a -> b -> (d, x, y)
gcdext :: Int -> Int -> (Int, Int, Int)
gcdext 0 b = (b, 0, 1)
gcdext a b =
  let (d, x, y) = gcdext (b `mod` a) a
  in (d, y - (b `div` a) * x, x)

invert :: Int -> Maybe Int
invert a =
  let (g, x, y) = gcdext a modulus
  in if g == 1
        then Just $ ((x `mod` modulus) + modulus) `mod` modulus
        else Nothing

toIntegerWithModulus :: Rational -> Int
toIntegerWithModulus r = ((((fromIntegral $ numerator r) + modulus) `mod` modulus) * (fromJust $ invert $ fromIntegral $ denominator r)) `mod` modulus

exponentGen :: GenFunc
exponentGen = Polynom [(fromIntegral 1) / (fromIntegral $ factorial n) | n <- [0..]]

sqrtGen :: GenFunc
sqrtGen = Polynom $ [((-1 % 1) ^^ n * (fromIntegral $ factorial (2*n)))/(fromIntegral $ (1 - 2*n) * (factorial n) ^ 2 * (4 ^ n)) | n <- [0..]]

lnGen :: GenFunc
lnGen = Polynom $ (0 % 1):[((-1 % 1) ^^ (n + 1)) / (fromIntegral n) | n <- [1..]]

main = do
  (n:m:[]) <- fmap (map (readInt) . words) getLine
  p <- fmap (Polynom . (map (fromIntegral . readInt)) . words) getLine
  mapM_ (\f -> putStrLn $ showRationals $ getFirstN m $ Subst f p) [sqrtGen, exponentGen, lnGen]
  return ()
  where
    showRationals = unwords . (map (show . toIntegerWithModulus))
