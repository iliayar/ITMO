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

filename = "factorial"

blk = "_"

ac = stateFromList "ac" []
rj = stateFromList "rj" []

s = stateFromFunc "s" tr
  where tr c = (prepare_fact, c, L)

prepare = stateFromFunc "prepare" tr
  where
    tr "_" = (right_to_dec, "+", T)
    tr c = (prepare, c, L)

prepare_fact = stateFromFunc "prepare_fact" tr
  where
    tr "_" = (copy_fact, "|", T)
    tr c = (prepare_fact, c, L)

-- copy_fact = right_to "_" copy_fact1 "copy_fact"
-- copy_fact1 = stateFromList "copy_fact1" [("_", copy_fact2, "_", L)]
copy_fact = stateFromFunc "copy_fact" tr
  where
    tr "_" = (copy_fact2, "_", L)
    tr "f0" = (copy_fact2, "f0", L)
    tr "f1" = (copy_fact2, "f1", L)
    tr c = (copy_fact, c, R)
copy_fact2 = stateFromList "copy_fact2"
  [ ("0", copy_fact_left0t, "f0", L)
  , ("1", copy_fact_left1t, "f1", L)
  , ("|", restore_fact, "|", T) ] -- FIXME
copy_fact_left0t = left_to "|" copy_fact_left0 "copy_fact_left0t"
copy_fact_left0 = stateFromFunc "copy_fact_left0" tr
  where
    tr "_" = (copy_fact, "t0", T)
    tr "-" = (copy_fact, "t0", T)
    tr "0" = (copy_fact, "t0", T)
    tr "1" = (copy_fact, "t0", T)
    tr c = (copy_fact_left0, c, L)
copy_fact_left1t = left_to "|" copy_fact_left1 "copy_fact_left1t"
copy_fact_left1 = stateFromFunc "copy_fact_left1" tr
  where
    tr "_" = (copy_fact, "t1", T)
    tr "-" = (copy_fact, "t1", T)
    tr "0" = (copy_fact, "t1", T)
    tr "1" = (copy_fact, "t1", T)
    tr c = (copy_fact_left1, c, L)
restore_fact = stateFromFunc "restore_fact" tr
  where
    tr "-" = (restore_fact1, "-", R)
    tr "_" = (restore_fact1, "_", R)
    tr "*" = (restore_fact1, "*", R)
    tr c = (restore_fact, c, L)
restore_fact1 = stateFromList "restore_fact1"
  [ ("t0", restore_fact1, "0", R)
  , ("t1", restore_fact1, "1", R)
  , ("f0", restore_fact1, "0", R)
  , ("f1", restore_fact1, "1", R)
  , ("|", restore_fact1, "|", R)
  , ("_", fact_mult, "_", L) ]
fact_mult = stateFromFunc "fact_mult" tr
  where
    tr "*" = (fact_mult1, "*", T)
    tr "_" = (fact_mult_init, "_", T)
    tr "-" = (fact_mult, "0", L)
    tr c = (fact_mult, c, L)
fact_mult_init = stateFromList "fact_mult_init" [ ("_", fact_mult_init1, "*", L) ]
fact_mult_init1 = stateFromList "fact_mult_init1" [ ("_", prepare, "1", T) ]
fact_mult1 = left_to "_" prepare "fact_mult1"

right_to_num0 = stateFromFunc "right_to_num0" tr
  where
    tr "*" = (right_to_num0t, "*", L)
    tr "r0" = (right_to_num0t, "r0", L)
    tr "r1" = (right_to_num0t, "r1", L)
    tr c = (right_to_num0, c, R)
right_to_num0t = stateFromList "right_to_num0t"
  [ ("0", left_to_add0, "r0", T)
  , ("1", left_to_add1, "r1", T)
  , ("+", clear_left, "+", T) ]
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

right_to_dec = right_to "|" right_to_dec1 "right_to_dec"
right_to_dec1 = stateFromList "right_to_dec1" [("|", dec, "|", L)]
dec = stateFromList "dec"
  [ ("0", dec, "1", L)
  , ("1", left_to_mul_add, "0", T)
  , ("*", clear_mul, "*", T) ]

left_to_mul_add = left_to "+" left_to_mul_add1 "left_to_mul_add"
left_to_mul_add1 = stateFromList "left_to_mul_add1" [("+", right_to_num0, "+", T)]


clear_mul = right_to "|" clear_mul1 "clear_mul"
clear_mul1 = stateFromList "clear_mul1" [("|", clear_mul2, "|", L)]
clear_mul2 = stateFromFunc "clear_mul2" tr
  where
    tr "+" = (clear_mul3, "*", L)
    tr c = (clear_mul2, "-", L)
clear_mul3 = left_to "_" clear_mul4 "clear_mul3"
clear_mul4 = stateFromList "clear_mul4" [("_", clear_mul5, "_", R)]
clear_mul5 = stateFromFunc "clear_mul5" tr
  where
    tr "_" = (right_to_fact, "0", T)
    tr c = (right_to_fact, c, T)

right_to_fact = right_to "|" right_to_fact1 "right_to_fact"
right_to_fact1 = stateFromList "right_to_fact1" [("|", right_to_dec_fact, "|", T) ]
right_to_dec_fact = right_to "_" right_to_dec_fact1 "right_to_dec_fact"
right_to_dec_fact1 = stateFromList "right_to_dec_fact1" [("_", dec_fact, "_", L) ]
dec_fact = stateFromList "dec_fact"
  [ ("0", dec_fact, "1", L)
  , ("1", check_fact_zero, "0", T)
  , ("|", clear_fact, "|", T) ] -- FIXME It means fact in initialy zero
left_to_fact_split = left_to "|" copy_fact "left_to_fact_split"
check_fact_zero = right_to "_" check_fact_zero1 "check_fact_zero"
check_fact_zero1 = stateFromList "check_fact_zero1" [("_", check_fact_zero2, "_", L)]
check_fact_zero2 = stateFromList "check_fact_zero2"
  [ ("0", check_fact_zero2, "0", L)
  , ("1", left_to_fact_split, "1", T)
  , ("|", clear_fact, "|", T) ] -- FIXME

clear_fact = stateFromFunc "clear_fact" tr
  where
    tr "_" = (clear_fact2, "_", T)
    tr c = (clear_fact, "_", R)
clear_fact2 = stateFromFunc "clear_fact2" tr
  where
    tr "*" = (clear_fact3, "_", L)
    tr c = (clear_fact2, "_", L)
clear_fact3 = stateFromFunc "clear_fact3" tr
  where
    tr "_" = (ac, "0", T)
    tr c = (clear_fact4, c, T)
clear_fact4 = left_to "_" clear_fact5 "clear_fact4"
clear_fact5 = stateFromList "clear_fact5" [("_", ac, "_", R)]
  
machine = Machine {
  states = [ s, ac, rj
           , prepare
           , prepare_fact
           , copy_fact
           , copy_fact2
           , copy_fact_left0t
           , copy_fact_left0
           , copy_fact_left1t
           , copy_fact_left1
           , restore_fact
           , restore_fact1
           , fact_mult
           , fact_mult_init
           , fact_mult_init1
           , fact_mult1
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
           , right_to_fact
           , right_to_fact1
           , right_to_dec_fact
           , right_to_dec_fact1
           , dec_fact
           , left_to_fact_split
           , check_fact_zero
           , check_fact_zero1
           , check_fact_zero2
           , clear_fact
           , clear_fact2
           , clear_fact3
           , clear_fact4
           , clear_fact5
                          ],
  start = s,
  accept = ac,
  reject = rj,
  blank = blk
                  }

main = do
    writeFile (filename ++ ".out") $ show machine
    let (Logger res l) = runMachineDefault (map (:[]) "1010") machine
    case res of
        Left err -> putStrLn $ "Error: " ++ err
        Right (verdict, state) -> putStrLn $ unlines [show verdict, name state]
    putStrLn l
