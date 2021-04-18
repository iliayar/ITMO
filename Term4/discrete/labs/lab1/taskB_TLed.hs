import Control.Monad
import Data.List
import Data.Ratio (numerator, denominator, (%))
import Data.Maybe (fromJust)

modulus :: Integral a => a
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
            getAll' (a:as) sum =
              let  (n:ns) = zipWith (+) sum $ map (*a) p2
              in n : getAll' as ns
        in getAll' p1 (repeat 0)
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
          (_:bs) = getAll g2
          bsp = Polynom bs
          getAll' (a:axs) gp sum =
            let bxs = map (*a) $ getAll gp
                (n:ns) = zipWith (+) sum bxs
            in n : getAll' axs (Mult gp bsp) ns
      in a : getAll' as bsp (repeat 0)
      

fromRational' :: (Rational -> Integer) -> Rational -> Int
fromRational' f = fromIntegral . (`mod` modulus) . f

factorial :: Int -> Int
factorial n = foldl (\a c -> (a * c) `mod` modulus) 1 [1..n]
factorialRat :: Int -> Rational
factorialRat = fromIntegral . factorial
comb n k = (factorial n) `div` ((factorial k) * (factorial $ n - k))

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
        then Just $ x `mod` modulus
        else Nothing

toIntegerWithModulus :: Rational -> Int
toIntegerWithModulus r = ((((fromRational' numerator r) + modulus) `mod` modulus) * (fromIntegral $ fromJust $ invert $ (fromRational' denominator r))) `mod` modulus

exponentGen :: GenFunc
exponentGen = Polynom [(1 % 1) / (factorialRat n) | n <- [0..]]

sqrtGen :: GenFunc
sqrtGen = Polynom $ [(((-1 % 1) ^^ n) * (factorialRat (2*n)))/((fromIntegral (1 - 2*n)) * (((factorialRat n) ^^ 2) * ((4 % 1) ^^ n))) | n <- [0..]]

lnGen :: GenFunc
lnGen = Polynom $ (0 % 1):[((-1 % 1) ^^ ((n + 1) `mod` 2)) / (fromIntegral n) | n <- [1..]]

main = do
  (n:m:[]) <- fmap (map read . words) getLine
  p <- fmap (Polynom . (map read) . words) getLine
  mapM_ (\f -> putStrLn $ showRationals $ getFirstN m $ Subst f p) [lnGen]
  return ()
  where
    showRationals = unwords . (map (show . toIntegerWithModulus))
