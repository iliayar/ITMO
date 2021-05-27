import Turing

import Control.Monad.Logger

ac = stateFromList "ac" []
rj = stateFromList "rj" []

--s = stateFromList "s"
    --[ ('_', ac, '_', T)
    --, ('0', n, '_', R) ]

--n = stateFromList "n"
    --[ ('_', rj, '_', T)
    --, ('0', s, '_', R) ]   

s = stateFromFunc "s" (\c -> (prestart, c, T))

prestart = stateFromFunc "prestart" (\c -> (right_to_plus_dec, c, R))

decrement_left_pre = stateFromList "decrement_left_pre"
    [ ('0', decrement_left_carry, '1', L)
    , ('1', right_to_plus, '0', R)]

decrement_left_carry = stateFromList "decrement_left_carry"
    [ ('1', right_to_plus, '0', R)
    , ('0', decrement_left_carry, '1', L)
    , ('_', right_to_plus_finish, '_', R)]

right_to_plus_dec = stateFromFunc "right_to_plus_dec" f
    where 
        f '+' = (decrement_left_pre, '+', L)
        f a = (right_to_plus_dec, a, R)

right_to_plus = stateFromFunc "right_to_plus" f
    where
        f '+' = (increment_right, '+', R)
        f a = (right_to_plus, a, R)

increment_right = stateFromFunc "increment_right" f
    where
        f '_' = (increment_left_pre, '_', L)
        f a = (increment_right, a, R)

increment_left_pre = stateFromList "increment_left_pre"
    [ ('0', left_to_plus, '1', L)
    , ('1', increment_left_carry, '0', L)]

increment_left_carry = stateFromList "increment_left_carry"
    [ ('0', left_to_plus, '1', L)
    , ('1', increment_left_carry, '0', L)
    , ('+', rmove_right_pre, '+', R)]

rmove_right_pre = stateFromFunc "rmove_right_pre" (\_ -> (rmove_right_blanking, '1', R))

rmove_right_blanking = stateFromFunc "rmove_right_blanking" f
    where
        f '_' = (left_to_plus, '0', L)
        f _ = (rmove_right_blanking, '0', R)

left_to_plus = stateFromList "left_to_plus"
    [ ('0', left_to_plus, '0', R)
    , ('1', left_to_plus, '1', L)
    , ('+', decrement_left_pre, '+', L)]

right_to_plus_finish = stateFromFunc "right_to_plus_finish" f
    where
        f '+' = (ac, '_', R)
        f _ = (right_to_plus_finish, '_', R)

machine = Machine {
    states = 
    [ s
    , ac
    , rj
    , prestart
    , decrement_left_pre
    , decrement_left_carry
    , right_to_plus_dec
    , right_to_plus
    , increment_right
    , increment_left_pre
    , increment_left_carry
    , rmove_right_pre
    , rmove_right_blanking
    , left_to_plus
    , right_to_plus_finish ],
    start = s,
    accept = ac,
    reject = rj,
    blank = '_' }

main = do 
    putStrLn $ show machine
    let (Logger res l) = runMachineDefault "01+10" machine
    case res of
        Left err -> putStrLn $ "Error: " ++ err
        Right (verdict, state) -> putStrLn $ unlines [show verdict, name state]
    putStrLn l
