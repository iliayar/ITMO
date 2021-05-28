import Turing

import Control.Monad.Logger

filename = "mirror"

blk = '_'

ac = stateFromList "ac" []
rj = stateFromList "rj" []

s = stateFromFunc "s" tr
  where tr c = (right_to_blank, c, T)

right_to = move_to R
left_to = move_to L
move_to d c f name = let right_to' = stateFromFunc name tr
                         tr c'
                           | c' == c = (f, c', T)
                           | otherwise = (right_to', c', d)
                     in right_to'

right_to_blank = right_to blk after_right_to_blank "right_to_blank"
after_right_to_blank = stateFromList "after_right_to_blank"
  [ (blk, move_to_copy_left, ':', T) ]

move_to_copy_left = left_to ':' start_copy_left1 "move_to_copy_left"
start_copy_left1 = stateFromList "start_copy_left1"
  [ (':', start_copy_left2, ':', L)]
start_copy_left2 = stateFromList "start_copy_left2"
  [ ('0', start_copy_left3t0, ':', R)
  , ('1', start_copy_left3t1, ':', R)
  , (blk, finish, blk, R) ] -- FIXME
start_copy_left3t0 = stateFromList "start_copy_left3t0"
  [ (':', start_copy_left, '0', T) ]
start_copy_left3t1 = stateFromList "start_copy_left3t1"
  [ (':', start_copy_left, '1', T) ]
start_copy_left = stateFromList "start_copy_left"
  [ ('0', copy_right0, '0', T)
  , ('1', copy_right1, '1', T)]

copy_right1 = right_to blk copy_right1t "copy_right1"
copy_right1t = stateFromList "copy_right1t"
  [ (blk, move_to_copy_left, '1', T) ]
copy_right0 = right_to blk copy_right0t "copy_right0"
copy_right0t = stateFromList "copy_right0t"
  [ (blk, move_to_copy_left, '0', T) ]

finish = stateFromList "finish"
  [ (':', ac, blk, R) ]


machine = Machine {
  states = s:ac:rj:[ right_to_blank
                   , after_right_to_blank
                   , move_to_copy_left
                   , start_copy_left1
                   , start_copy_left2
                   , start_copy_left3t0
                   , start_copy_left3t1
                   , start_copy_left
                   , copy_right1
                   , copy_right1t
                   , copy_right0
                   , copy_right0t
                   , finish
                   ],
  start = s,
  accept = ac,
  reject = rj,
  blank = blk
                  }

main = do 
    writeFile (filename ++ ".out") $ show machine
    let (Logger res l) = runMachineDefault "10100" machine
    case res of
        Left err -> putStrLn $ "Error: " ++ err
        Right (verdict, state) -> putStrLn $ unlines [show verdict, name state]
    putStrLn l
