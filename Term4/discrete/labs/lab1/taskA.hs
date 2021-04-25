import Control.Monad

modulus = 998244353

data Rat = Polynom [Rational] 
              | Mult Rat Rat 
              | Sum Rat Rat 
              | Div Rat Rat
    deriving (Show)

class Gen a where
    getAll :: a -> [Rational]
    getFirstN :: Int -> a -> [Rational]
    getFirstN n = (take n) . getAll

paddZeros = (++(repeat 0))
take' n = (take n) . paddZeros

instance Gen Rat where
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

main = do
    (n:m:[]) <- fmap ((map readInt) . words) $ getLine
    p1 <- fmap (Polynom . (map $ fromIntegral . readInt) . words) getLine
    p2 <- fmap (Polynom . (map $ fromIntegral . readInt) . words) getLine
    putStrLn $ show (max n m)
    putStrLn $ unwords $ map showRationals $ getFirstN (1 + max n m) $ Sum p1 p2
    putStrLn $ show (n + m)
    putStrLn $ unwords $ map showRationals $ getFirstN (n + m + 1) $ Mult p1 p2
    putStrLn $ unwords $ map showRationals $ getFirstN 1000 $ Div p1 p2
  where
    showRationals = show . (`mod` modulus) . floor
