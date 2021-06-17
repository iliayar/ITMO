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

filename = "convertto2"

blk = "_"

ac = stateFromList "ac" []
rj = stateFromList "rj" []

s = stateFromFunc "s" tr
  where tr c = (split, c, L)

split = stateFromList "split" [ ("_", split1, "#", L) ]
split1 = stateFromList "splt1" [ ("_", to_end, "0", T)]
to_end = right_to "_" dec1 "to_end"
to_begin = left_to "_" to_begin1 "to_begin"
to_begin1 = stateFromList "to_begin1" [ ("_", ac, "_", R) ]
dec1 = stateFromList "dec1" [ ("_", dec, "_", L) ]
dec = stateFromList "dec"
  [ ("0", dec, "2", L)
  , ("1", to_split, "0", T)
  , ("2", to_split, "1", T)
  , ("#", clear, "#", T) ]
to_split = left_to "#" to_splt1 "to_split"
to_splt1 = stateFromList "to_split1" [ ("#", inc, "#", L) ]
inc = stateFromList "inc"
  [ ("0", to_end, "1", T)
  , ("1", inc, "0", L)
  , ("_", to_end, "1", T) ]
clear = right_to "_" clear1 "clear"
clear1 = stateFromList "clear1" [ ("_", clear2, "_", L) ]
clear2 = stateFromFunc "clear2" tr
  where
    tr "#" = (to_begin, "_", L)
    tr c = (clear2, "_", L)
  

machine = Machine {
  states = [ s, ac, rj
           , split
           , split1
           , to_end
           , to_begin
           , to_begin1
           , dec1
           , dec
           , to_split
           , to_splt1
           , inc
           , clear
           , clear1
           , clear2
                          ],
  start = s,
  accept = ac,
  reject = rj,
  blank = blk
                  }

main = do
    writeFile (filename ++ ".out") $ show machine
    let (Logger res l) = runMachineDefault (map (:[]) "1") machine
    case res of
        Left err -> putStrLn $ "Error: " ++ err
        Right (verdict, state) -> putStrLn $ unlines [show verdict, name state]
    putStrLn l
