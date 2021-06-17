import TuringStrings


inv_dir R = L
inv_dir L = R
inv_dir T = T

right_to = move_to R
left_to = move_to L
move_to d c f name = let move_to' = stateFromFunc name tr
                         tr c'
                           | c' == c = (f, c', T)
                           | otherwise = (move_to', c', d)
                     in move_to'
swap_to d alphl cr f name = let
    left_fns = zipWith (\ a n
      -> stateFromFunc
           (name ++ "_left_fns_" ++ show n) (const (f, a, d))) alphl [0..]
    left_fn = stateFromList (name ++ "_left_fn") $ map (\(a, n) -> (a, left_fns !! n, cr, inv_dir d)) $ zip alphl [0..]
    right_fn = stateFromFunc (name ++ "_right_fn") (\c -> (left_fn, c, d))
  in [right_fn, left_fn] ++ left_fns

swap_left = swap_to L
swap_right = swap_to R

filename = "multiplication"

blk = "_"

ac = stateFromList "ac" []
rj = stateFromList "rj" []

s = stateFromFunc "s" tr
  where tr c = (prepare, c, L)

prepare = stateFromFunc "prepare" tr
  where
    tr "_" = (right_to_dec, "+", T)
    tr c = (prepare, c, L)

right_to_num0 = stateFromFunc "right_to_num0" tr
  where
    tr "*" = (right_to_num0t, "*", L)
    tr "r0" = (right_to_num0t, "r0", L)
    tr "r1" = (right_to_num0t, "r1", L)
    tr c = (right_to_num0, c, R)
right_to_num0t = stateFromList "right_to_num0t"
  [ ("0", left_to_add0, "r0", T)
  , ("1", left_to_add1, "r1", T)
  , ("+", clear_left, "+", T) ] -- FIXME
left_to_add0 = stateFromFunc "left_to_add0" tr
  where
    tr "+" = (left_to_add0t, "+", T)
    tr c = (left_to_add0, c, L)
left_to_add0t = stateFromFunc "left_to_add0t" tr
  where
    tr "1" = (add0, "1", T)
    tr "0" = (add0, "0", T)
    tr "_" = (add0, "_", T)
    tr c = (left_to_add0t, c, L)
add0 = stateFromList "add0"
  [ ("1", right_to_num0, "l1", T)
  , ("0", right_to_num0, "l0", T)
  , ("_", right_to_num0, "l0", T)]

      
right_to_num1 = stateFromFunc "right_to_num1" tr
  where
    tr "*" = (right_to_num1t, "*", L)
    tr "r0" = (right_to_num1t, "r0", L)
    tr "r1" = (right_to_num1t, "r1", L)
    tr c = (right_to_num1, c, R)
right_to_num1t = stateFromList "right_to_num1t"
  [ ("0", left_to_add1, "r0", T)
  , ("1", left_to_add10, "r1", T)
  , ("+", left_to_add1, "+", T) ]
left_to_add1 = stateFromFunc "left_to_add1" tr
  where
    tr "+" = (left_to_add1t, "+", T)
    tr c = (left_to_add1, c, L)
left_to_add1t = stateFromFunc "left_to_add1t" tr
  where
    tr "1" = (add1, "1", T)
    tr "0" = (add1, "0", T)
    tr "_" = (add1, "_", T)
    tr c = (left_to_add1t, c, L)
add1 = stateFromList "add1"
  [ ("1", right_to_num1, "l0", T)
  , ("0", right_to_num0, "l1", T)
  , ("_", right_to_num0, "l1", T)]


right_to_num10 = stateFromFunc "right_to_num10" tr
  where
    tr "*" = (right_to_num10t, "*", L)
    tr "r0" = (right_to_num10t, "r0", L)
    tr "r1" = (right_to_num10t, "r1", L)
    tr c = (right_to_num10, c, R)
right_to_num10t = stateFromList "right_to_num10t"
  [ ("0", left_to_add10, "r0", T)
  , ("1", rj, "r1", T)
  , ("+", left_to_add10, "+", T) ]
left_to_add10 = stateFromFunc "left_to_add10" tr
  where
    tr "+" = (left_to_add10t, "+", T)
    tr c = (left_to_add10, c, L)
left_to_add10t = stateFromFunc "left_to_add10t" tr
  where
    tr "1" = (add10, "1", T)
    tr "0" = (add10, "0", T)
    tr "_" = (add10, "_", T)
    tr c = (left_to_add10t, c, L)
add10 = stateFromList "add10"
  [ ("1", right_to_num1, "l1", T)
  , ("0", right_to_num1, "l0", T)
  , ("_", right_to_num1, "l0", T)]

clear_left = left_to "_" clear_left1 "clear_left"
clear_left1 = stateFromList "clear_left1" [("_", clear, "_", R)]
clear = stateFromFunc "clear" tr
  where
    tr "*" = (right_to_dec, "*", T)
    tr "l0" = (clear, "0", R)
    tr "l1" = (clear, "1", R)
    tr "r0" = (clear, "0", R)
    tr "r1" = (clear, "1", R)
    tr c = (clear, c, R)

right_to_dec = right_to "_" right_to_dec1 "right_to_dec"
right_to_dec1 = stateFromList "right_to_dec1" [("_", dec, "_", L)]
dec = stateFromList "dec"
  [ ("0", dec, "1", L)
  , ("1", left_to_mul_add, "0", T)
  , ("*", clear_mul, "*", T) ]

left_to_mul_add = left_to "+" left_to_mul_add1 "left_to_mul_add"
left_to_mul_add1 = stateFromList "left_to_mul_add1" [("+", right_to_num0, "+", T)]


clear_mul = right_to "_" clear_mul1 "clear_mul"
clear_mul1 = stateFromList "clear_mul1" [("_", clear_mul2, "_", L)]
clear_mul2 = stateFromFunc "clear_mul2" tr
  where
    tr "+" = (clear_mul3, "_", L)
    tr c = (clear_mul2, "_", L)
clear_mul3 = left_to "_" clear_mul4 "clear_mul3"
clear_mul4 = stateFromList "clear_mul4" [("_", clear_mul5, "_", R)]
clear_mul5 = stateFromFunc "clear_mul5" tr
  where
    tr "_" = (ac, "0", T)
    tr c = (ac, c, T)

machine = Machine {
  states = [ s, ac, rj
           , prepare
           , right_to_num0
           , right_to_num0t
           , left_to_add0
           , left_to_add0t
           , add0
           , right_to_num1
           , right_to_num1t
           , left_to_add1
           , left_to_add1t
           , add1
           , right_to_num10
           , right_to_num10t
           , left_to_add10
           , left_to_add10t
           , add10
           , clear_left
           , clear_left1
           , clear
           , right_to_dec
           , right_to_dec1
           , dec
           , left_to_mul_add
           , left_to_mul_add1
           , clear_mul
           , clear_mul1
           , clear_mul2
           , clear_mul3
           , clear_mul4
           , clear_mul5
                          ],
  start = s,
  accept = ac,
  reject = rj,
  blank = blk
                  }

main = do
    writeFile (filename ++ ".out") $ show machine
    let (Logger res l) = runMachineDefault (map (:[]) "101*1") machine
    case res of
        Left err -> putStrLn $ "Error: " ++ err
        Right (verdict, state) -> putStrLn $ unlines [show verdict, name state]
    putStrLn l
