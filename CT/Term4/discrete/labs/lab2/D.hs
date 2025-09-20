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

filename = "tandem"

blk = '_'

ac = stateFromList "ac" []
rj = stateFromList "rj" []

s = stateFromFunc "s" tr
  where tr c = (convert_right, c, T)

convert_right = stateFromFunc "convert_right" tr
  where
    tr '0' = (convert_right_move, '2', R)
    tr '1' = (convert_right_move, '3', R)
    tr '4' = (move_to_end, '4', T)
    tr '5' = (move_to_end, '5', T)
    tr c = (rj, c, T)


convert_right_move = stateFromFunc "convert_right_move" tr
  where
    tr '0' = (convert_right_move, '0', R)
    tr '1' = (convert_right_move, '1', R)
    tr '_' = (convert_left, '_', L)
    tr '4' = (convert_left, '4', L)
    tr '5' = (convert_left, '5', L)
    tr c = (rj, c, T)

convert_left = stateFromFunc "convert_left" tr
  where
    tr '0' = (convert_left_move, '4', L)
    tr '1' = (convert_left_move, '5', L)
    tr '2' = (move_to_end, '2', T)
    tr '3' = (move_to_end, '3', T)
    tr c = (rj, c, T)

convert_left_move = stateFromFunc "convert_left_move" tr
  where
    tr '0' = (convert_left_move, '0', L)
    tr '1' = (convert_left_move, '1', L)
    tr '_' = (convert_right, '_', R)
    tr '2' = (convert_right, '2', R)
    tr '3' = (convert_right, '3', R)
    tr c = (rj, c, T)

move_to_end = right_to '_' move_to_end_quote "move_to_end"
move_to_end_quote = stateFromFunc "move_to_end_quote" tr
  where
    tr c = (check_left, c, L)

check_left = stateFromList "check_left"
  [ ('4', check_left0, '0', L)
  , ('5', check_left1, '1', L)
  , ('1', check_left, '1', L)
  , ('0', check_left, '0', L)
  , ('_', ac, '_', R) ]

check_left1 = stateFromFunc "check_left1" tr
  where
    tr '2' = (rj, '2', T)
    tr '3' = (move_to_end, '1', T)
    tr c = (check_left1, c, L)
check_left0 = stateFromFunc "check_left0" tr
  where
    tr '3' = (rj, '3', T)
    tr '2' = (move_to_end, '0', T)
    tr c = (check_left0, c, L)

machine = Machine {
  states = [ s, ac, rj
      , convert_right
      , convert_right_move
      , convert_left
      , convert_left_move
      , move_to_end
      , move_to_end_quote
      , check_left
      , check_left1
      , check_left0
                          ],
  start = s,
  accept = ac,
  reject = rj,
  blank = blk
                  }

main = do
    writeFile (filename ++ ".out") $ show machine
    let (Logger res l) = runMachineDefault "101101" machine
    case res of
        Left err -> putStrLn $ "Error: " ++ err
        Right (verdict, state) -> putStrLn $ unlines [show verdict, name state]
    putStrLn l
