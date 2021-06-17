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

filename = "less"

blk = '_'

ac = stateFromList "ac" []
rj = stateFromList "rj" []

s = stateFromFunc "s" tr
  where tr c = (to_end_eq, c, T)

to_end_eq = right_to '_' to_end1_eq "to_end_eq"
to_end1_eq = stateFromList "to_end1_eq" [('_', start_cmp_right_eq, '_', L)]
to_end_gt = right_to '_' to_end1_gt "to_end_gt"
to_end1_gt = stateFromList "to_end1_gt" [('_', start_cmp_right_gt, '_', L)]
to_end_lt = right_to '_' to_end1_lt "to_end_lt"
to_end1_lt = stateFromList "to_end1_lt" [('_', start_cmp_right_lt, '_', L)]

start_cmp_right_eq = stateFromList "start_cmp_right_eq"
  [ ('1', move_cmp_left1_eq, '_', T)
  , ('0', move_cmp_left0_eq, '_', T)
  , ('<', fin_left_eq, '<', T) ]
start_cmp_right_gt = stateFromList "start_cmp_right_gt"
  [ ('1', move_cmp_left1_gt, '_', T)
  , ('0', move_cmp_left0_gt, '_', T)
  , ('<', fin_left_gt, '<', T) ]
start_cmp_right_lt = stateFromList "start_cmp_right_lt"
  [ ('1', move_cmp_left1_lt, '_', T)
  , ('0', move_cmp_left0_lt, '_', T)
  , ('<', fin_left_lt, '<', T) ]

move_cmp_left1_eq = stateFromFunc "move_cmp_left1_eq" tr
  where
    tr '<' = (move_cmp_left1t_eq, '<', L)
    tr c = (move_cmp_left1_eq, c, L)
move_cmp_left1t_eq = stateFromList "move_cmp_left1t_eq"
    [ ('-', move_cmp_left1t_eq, '-', L)
    , ('1', to_end_eq, '-', T)
    , ('0', to_end_lt, '-', T)
    , ('_', to_end_lt, '-', T) ]
move_cmp_left0_eq = stateFromFunc "move_cmp_left0_eq" tr
  where
    tr '<' = (move_cmp_left0t_eq, '<', L)
    tr c = (move_cmp_left0_eq, c, L)
move_cmp_left0t_eq = stateFromList "move_cmp_left0t_eq"
    [ ('-', move_cmp_left0t_eq, '-', L)
    , ('1', to_end_gt, '-', T)
    , ('0', to_end_eq, '-', T)
    , ('_', to_end_eq, '-', T) ]

move_cmp_left1_gt = stateFromFunc "move_cmp_left1_gt" tr
  where
    tr '<' = (move_cmp_left1t_gt, '<', L)
    tr c = (move_cmp_left1_gt, c, L)
move_cmp_left1t_gt = stateFromList "move_cmp_left1t_gt"
    [ ('-', move_cmp_left1t_gt, '-', L)
    , ('1', to_end_gt, '-', T)
    , ('0', to_end_lt, '-', T)
    , ('_', to_end_lt, '-', T) ]
move_cmp_left0_gt = stateFromFunc "move_cmp_left0_gt" tr
  where
    tr '<' = (move_cmp_left0t_gt, '<', L)
    tr c = (move_cmp_left0_gt, c, L)
move_cmp_left0t_gt = stateFromList "move_cmp_left0t_gt"
    [ ('-', move_cmp_left0t_gt, '-', L)
    , ('1', to_end_gt, '-', T)
    , ('0', to_end_gt, '-', T)
    , ('_', to_end_gt, '-', T) ]

move_cmp_left1_lt = stateFromFunc "move_cmp_left1_lt" tr
  where
    tr '<' = (move_cmp_left1t_lt, '<', L)
    tr c = (move_cmp_left1_lt, c, L)
move_cmp_left1t_lt = stateFromList "move_cmp_left1t_lt"
    [ ('-', move_cmp_left1t_lt, '-', L)
    , ('1', to_end_lt, '-', T)
    , ('0', to_end_lt, '-', T)
    , ('_', to_end_lt, '-', T) ]
move_cmp_left0_lt = stateFromFunc "move_cmp_left0_lt" tr
  where
    tr '<' = (move_cmp_left0t_lt, '<', L)
    tr c = (move_cmp_left0_lt, c, L)
move_cmp_left0t_lt = stateFromList "move_cmp_left0t_lt"
    [ ('-', move_cmp_left0t_lt, '-', L)
    , ('1', to_end_gt, '-', T)
    , ('0', to_end_lt, '-', T)
    , ('_', to_end_lt, '-', T) ]


fin_left_eq = stateFromFunc "fin_left_eq" tr
  where
    tr '0' = (rj, '0', T)
    tr '_' = (rj, '_', T)
    tr '1' = (rj, '1', T)
    tr c = (fin_left_eq, c, L)
fin_left_lt = stateFromFunc "fin_left_lt" tr
  where
    tr '0' = (rj, '0', T)
    tr '_' = (ac, '_', T)
    tr '1' = (rj, '1', T)
    tr c = (fin_left_lt, c, L)
fin_left_gt = stateFromFunc "fin_left_gt" tr
  where
    tr '0' = (rj, '0', T)
    tr '_' = (rj, '_', T)
    tr '1' = (rj, '1', T)
    tr c = (fin_left_gt, c, L)

machine = Machine {
  states = [ s, ac, rj
           , to_end_eq
           , to_end1_eq
           , to_end_gt
           , to_end1_gt
           , to_end_lt
           , to_end1_lt
           , start_cmp_right_eq
           , start_cmp_right_gt
           , start_cmp_right_lt
           , move_cmp_left1_eq
           , move_cmp_left1t_eq
           , move_cmp_left0_eq
           , move_cmp_left0t_eq
           , move_cmp_left1_gt
           , move_cmp_left1t_gt
           , move_cmp_left0_gt
           , move_cmp_left0t_gt
           , move_cmp_left1_lt
           , move_cmp_left1t_lt
           , move_cmp_left0_lt
           , move_cmp_left0t_lt
           , fin_left_eq
           , fin_left_lt
           , fin_left_gt
                          ],
  start = s,
  accept = ac,
  reject = rj,
  blank = blk
                  }

main = do
    writeFile (filename ++ ".out") $ show machine
    let (Logger res l) = runMachineDefault "0<10101" machine
    case res of
        Left err -> putStrLn $ "Error: " ++ err
        Right (verdict, state) -> putStrLn $ unlines [show verdict, name state]
    putStrLn l
