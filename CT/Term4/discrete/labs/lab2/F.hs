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

filename = "reverse"

blk = '_'

ac = stateFromList "ac" []
rj = stateFromList "rj" []

s = stateFromFunc "s" tr
  where tr c = (right_to_end, c, T)

right_to_end = right_to '_' left_border "right_to_end"
left_border = stateFromList "left_border" [ ('_', left_to_dias, '#', T) ]

left_to_dias = left_to '#' copy_begin "left_to_dias"
copy_begin = stateFromList "copy_begin" [ ('#', copy_begin1, '-', L) ]

copy_begin1 = stateFromList "copy_begin1"
  [ ('1', move_left1, '#', T)
  , ('0', move_left0, '#', T)
  , ('_', clear_right, '_', R) ]

move_left1 = stateFromFunc "move_left1" tr
  where
    tr '_' = (left_to_dias, '1', T)
    tr c = (move_left1, c, R)
move_left0 = stateFromFunc "move_left0" tr
  where
    tr '_' = (left_to_dias, '0', T)
    tr c = (move_left0, c, R)

clear_right = stateFromFunc "clear_right" tr
  where
    tr '-' = (clear_right, '_', R)
    tr c = (ac, c, T)

machine = Machine {
  states = [ s, ac, rj
           , right_to_end
           , left_border
           , left_to_dias
           , copy_begin
           , copy_begin1
           , move_left1
           , move_left0
           , clear_right
                          ],
  start = s,
  accept = ac,
  reject = rj,
  blank = blk
                  }

main = do
    writeFile (filename ++ ".out") $ show machine
    let (Logger res l) = runMachineDefault "100" machine
    case res of
        Left err -> putStrLn $ "Error: " ++ err
        Right (verdict, state) -> putStrLn $ unlines [show verdict, name state]
    putStrLn l
