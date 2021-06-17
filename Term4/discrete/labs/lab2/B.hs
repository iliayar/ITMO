import Turing

filename = "aplusb"

blk = '_'

ac = stateFromList "ac" []
rj = stateFromList "rj" []

s = stateFromFunc "s" tr
  where tr c = (right_to_plus, c, T)

right_to_plus = stateFromFunc "right_to_plus" tr
  where
    tr '+' = (check_last_right0, '#', L)
    tr c = (right_to_plus, c, R)

check_last_right0 = stateFromList "check_last_right0"
  [ ('0', right_to_blank_or_delim0, '$', T)
  , ('1', right_to_blank_or_delim1, '$', T)
  , ('^', right_to_blank_or_delim0, '^', R)
  , ('_', right_to_blank_or_delim0, '^', R)
  ]

check_last_right1 = stateFromList "check_last_right1"
  [ ('0', right_to_blank_or_delim1, '$', T)
  , ('1', right_to_blank_or_delim10, '$', T)
  , ('^', right_to_blank_or_delim1, '^', R)
  , ('_', right_to_blank_or_delim1, '^', R)
  ]

right_to_blank_or_delim0 = stateFromFunc "right_to_blank_or_delim0" tr
  where
    tr '_' = (add_last0, '_', L)
    tr ':' = (add_last0, ':', L)
    tr c = (right_to_blank_or_delim0, c, R)

right_to_blank_or_delim1 = stateFromFunc "right_to_blank_or_delim1" tr
  where
    tr '_' = (add_last1, '_', L)
    tr ':' = (add_last1, ':', L)
    tr c = (right_to_blank_or_delim1, c, R)

right_to_blank_or_delim10 = stateFromFunc "right_to_blank_or_delim10" tr
  where
    tr '_' = (add_last10, '_', L)
    tr ':' = (add_last10, ':', L)
    tr c = (right_to_blank_or_delim10, c, R)

add_last0 = stateFromList "add_last0"
  [ ('1', add_last0t1, ':', R)
  , ('0', add_last0t0, ':', R)
  , ('#', add_last0t0, ':', R)
  , ('^', right_to1, ':', T) ]
add_last0t1 = stateFromFunc "add_last0t1" tr
  where
    tr c = (left_to_dollar0, '1', L)
add_last0t0 = stateFromFunc "add_last0t0" tr
  where
    tr c = (left_to_dollar0, '0', L)

add_last1 = stateFromList "add_last1"
  [ ('1', add_last1t1, ':', R)
  , ('0', add_last1t0, ':', R)
  , ('#', add_last1t0, ':', R) ]
add_last1t1 = stateFromFunc "add_last1t1" tr
  where
    tr c = (left_to_dollar1, '0', L)
add_last1t0 = stateFromFunc "add_last1t0" tr
  where
    tr c = (left_to_dollar0, '1', L)

add_last10 = stateFromList "add_last10"
  [ ('1', add_last10t1, ':', R)
  , ('0', add_last10t0, ':', R)
  , ('#', add_last10t0, ':', R) ]
add_last10t1 = stateFromFunc "add_last10t1" tr
  where
    tr c = (left_to_dollar1, '1', L)
add_last10t0 = stateFromFunc "add_last10t0" tr
  where
    tr c = (left_to_dollar1, '0', L)

left_to_dollar0 = stateFromFunc "left_to_dollar0" tr
  where
    tr '$' = (check_last_right0, '#', L)
    tr '^' = (check_last_right0, '^', T)
    tr c = (left_to_dollar0, c, L)

left_to_dollar1 = stateFromFunc "left_to_dollar1" tr
  where
    tr '$' = (check_last_right1, '#', L)
    tr '^' = (check_last_right1, '^', T)
    tr c = (left_to_dollar1, c, L)

right_to1 = stateFromFunc "right_to1" tr
  where
    tr '1' = (ac, '1', T)
    tr '_' = (ac, '0', T)
    tr c = (right_to1, '_', R)

machine = Machine {
  states = s:ac:rj:[ right_to_plus
                   , check_last_right0
                   , check_last_right1
                   , right_to_blank_or_delim0
                   , right_to_blank_or_delim1
                   , right_to_blank_or_delim10
                   , add_last0
                   , add_last0t1
                   , add_last0t0
                   , add_last1
                   , add_last1t1
                   , add_last1t0
                   , add_last10
                   , add_last10t1
                   , add_last10t0
                   , left_to_dollar0
                   , left_to_dollar1
                   , right_to1
                   ],
  start = s,
  accept = ac,
  reject = rj,
  blank = blk
                  }

main = do 
    writeFile (filename ++ ".out") $ show machine
    let (Logger res l) = runMachineDefault "101+1010" machine
    case res of
        Left err -> putStrLn $ "Error: " ++ err
        Right (verdict, state) -> putStrLn $ unlines [show verdict, name state]
    putStrLn l
