import Turing


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

filename = "balanced"

blk = '_'

ac = stateFromList "ac" []
rj = stateFromList "rj" []

s = stateFromFunc "s" tr
  where tr c = (sums !! 0, c, T)

sums = map st [0..200]
  where
    st n
      | n == 0 = stateFromList ("sums_" ++ (show n))
                 [ (')', rj, ')', T)
                 , ('(', sums !! (n + 1), '(', R)
                 , ('_', ac, '_', T) ]
      | n < 200 = stateFromList ("sums" ++ (show n))
                 [ (')', sums !! (n - 1), ')', R)
                 , ('(', sums !! (n + 1), '(', R) ]
      | otherwise = rj


machine = Machine {
  states = [ s, ac, rj
                          ] ++ sums,
  start = s,
  accept = ac,
  reject = rj,
  blank = blk
                  }

main = do
    writeFile (filename ++ ".out") $ show machine
    let (Logger res l) = runMachineDefault "()()(()(((())))" machine
    case res of
        Left err -> putStrLn $ "Error: " ++ err
        Right (verdict, state) -> putStrLn $ unlines [show verdict, name state]
    putStrLn l
