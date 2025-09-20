import System.IO
import Data.List

log2 :: Int -> Int
log2 1 = 0
log2 x =  1 + log2 (div x 2)

dp :: Int -> [Int] -> [[Int]]
dp i prev
    | i == 0 = [prev]
    | otherwise = prev : dp (i - 1) next
        where next = map (prev !!) prev

dpPrint :: [[Int]] -> [IO ()]
dpPrint dp = map
                 (\(i, x) -> (putStr $ show i) >> (putStr ": ") >> (sequence x) >> (putStrLn ""))
                 $ zip [1..] $ map ((map $ (\x -> (putStr $ show x) >> (putStr " "))) . (filter (/= 0))) dp

readP :: String -> [Int]
readP str = map read $ words str
  
main = do
    n <- getLine
    pString <- getLine
    sequence $ dpPrint $ tail (transpose $ dp (log2 $ read n + 1) (0:(readP pString)))
