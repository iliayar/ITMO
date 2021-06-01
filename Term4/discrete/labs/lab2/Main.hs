import TuringMulti


inv_dir R = L
inv_dir L = R
inv_dir T = T

-- right_to = move_to R
-- left_to = move_to L
-- move_to d c f name = let move_to' = stateFromFunc name tr
--                          tr c'
--                            | c' == c = (f, c', T)
--                            | otherwise = (move_to', c', d)
--                      in move_to'
-- swap_to d alphl cr f name = let
--     left_fns = zipWith (\ a n
--       -> stateFromFunc
--            (name ++ "_left_fns_" ++ show n) (const (f, a, d))) alphl [0..]
--     left_fn = stateFromList (name ++ "_left_fn") $ map (\(a, n) -> (a, left_fns !! n, cr, inv_dir d)) $ zip alphl [0..]
--     right_fn = stateFromFunc (name ++ "_right_fn") (\c -> (left_fn, c, d))
--   in [right_fn, left_fn] ++ left_fns

-- swap_left = swap_to L
-- swap_right = swap_to R

filename = "factorial"

blk = "_"

ac = stateFromList "AC" []
rj = stateFromList "RJ" []

s = stateFromFunc "S" tr
  where tr (c1:c2:[]) = (step, [(c1, T), (c2, T)])

step = stateFromFunc "step" tr
  where
    tr ("0":c:[]) = (step, [("0", R), ("0", R)])
    tr ("1":c:[]) = (step, [("1", R), ("1", R)])
    tr ("a":c:[]) = (mt_and, [("a", R), (c, T)])
    tr ("o":c:[]) = (mt_or, [("o", R), (c, T)])
    tr ("_":c:[]) = (ac, [(c, T), (c, T)])

mt_and = stateFromFunc "and" tr
  where
    tr (c1:c2:[]) = (and1, [(c1, T), (c2, L)])
and1 = stateFromFunc "and1" tr
  where
    tr (c:"1":[]) = (and1_1, [(c, T), ("_", L)])
    tr (c:"0":[]) = (and1_0, [(c, T), ("_", L)])
and1_0 = stateFromFunc "and1_0" tr
  where
    tr (c:"1":[]) = (and1_01, [(c, T), ("_", T)])
    tr (c:"0":[]) = (and1_00, [(c, T), ("_", T)])
and1_1 = stateFromFunc "and1_1" tr
  where
    tr (c:"1":[]) = (and1_11, [(c, T), ("_", T)])
    tr (c:"0":[]) = (and1_10, [(c, T), ("_", T)])
and1_00 = stateFromFunc "and1_00" (\ (c:"_":[]) -> (step, [(c, R), ("0", R)]))
and1_01 = stateFromFunc "and1_01" (\ (c:"_":[]) -> (step, [(c, R), ("0", R)]))
and1_10 = stateFromFunc "and1_10" (\ (c:"_":[]) -> (step, [(c, R), ("0", R)]))
and1_11 = stateFromFunc "and1_11" (\ (c:"_":[]) -> (step, [(c, R), ("1", R)]))
  
mt_or = stateFromFunc "or" tr
  where
    tr (c1:c2:[]) = (or1, [(c1, T), (c2, L)])
or1 = stateFromFunc "or1" tr
  where
    tr (c:"1":[]) = (or1_1, [(c, T), ("_", L)])
    tr (c:"0":[]) = (or1_0, [(c, T), ("_", L)])
or1_0 = stateFromFunc "or1_0" tr
  where
    tr (c:"1":[]) = (or1_01, [(c, T), ("_", T)])
    tr (c:"0":[]) = (or1_00, [(c, T), ("_", T)])
or1_1 = stateFromFunc "or1_1" tr
  where
    tr (c:"1":[]) = (or1_11, [(c, T), ("_", T)])
    tr (c:"0":[]) = (or1_10, [(c, T), ("_", T)])
or1_00 = stateFromFunc "or1_00" (\ (c:"_":[]) -> (step, [(c, R), ("0", R)]))
or1_01 = stateFromFunc "or1_01" (\ (c:"_":[]) -> (step, [(c, R), ("1", R)]))
or1_10 = stateFromFunc "or1_10" (\ (c:"_":[]) -> (step, [(c, R), ("1", R)]))
or1_11 = stateFromFunc "or1_11" (\ (c:"_":[]) -> (step, [(c, R), ("1", R)]))

machine = Machine {
  states = [ s, ac, rj
                          ],
  start = s,
  accept = ac,
  reject = rj,
  blank = blk
                  }

main = do
    writeFile (filename ++ ".out") $ show machine
    let (Logger res l) = runMachineDefault (map (map (:[])) ["10a1o", "_"]) machine
    case res of
        Left err -> putStrLn $ "Error: " ++ err
        Right (verdict, state) -> putStrLn $ unlines [show verdict, name state]
    putStrLn l
