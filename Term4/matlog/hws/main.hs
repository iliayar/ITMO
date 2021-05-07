
data Rec = Z
        | N 
        | S Rec [Rec]
        | P Int 
        | R Rec Rec


eval :: Rec -> [Int] -> Int
eval Z (_:[]) = 0
eval N (x:[]) =  x + 1
eval (S g fs) xs = eval g $ map (\f -> eval f xs) fs
eval (P i) xs = xs !! (i - 1)
eval (R f g) (0:xs) = eval f xs
eval (R f g) (y:xs) = eval g $ (y - 1):(eval (R f g) $ (y-1):xs):xs

sumR = R (P 1) (S N [P 2])
multR = R Z (S sumR [P 2, P 3]) -- 10.1.a
decR = S (R Z (P 1)) [P 1, Z] -- 10.1.b
subR' i j = S (R (P 1) (S decR [P 2])) [P j, P i]
subR = S (R (P 1) (S decR [P 2])) [P 2, P 1] -- 10.1.c

divR' = S (R Z (S N [divR'])) [subR' 3 4, subR' 3 4, P 4]
divR = S divR' [P 1, Z, P 1, P 2]

main = do
    putStrLn $ show $ eval divR [50, 25]

