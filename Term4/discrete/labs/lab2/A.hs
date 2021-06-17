import Turing

filename = "zero"

blk = '_'

ac = stateFromList "ac" []
rj = stateFromList "rj" []

s = stateFromList "s"
  [ (blk, ac, blk, T)
  , ('0', n, blk, R)
  ]

n = stateFromList "n"
  [ ('0', s, blk, R)
  , (blk, rj, blk, R)
  ]

machine = Machine {
  states = [ s
           , ac
           , rj
           , n
           ],
  start = s,
  accept = ac,
  reject = rj,
  blank = blk
                  }

main = do 
    writeFile (filename ++ ".out") $ show machine
    let (Logger res l) = runMachineDefault "01+10" machine
    case res of
        Left err -> putStrLn $ "Error: " ++ err
        Right (verdict, state) -> putStrLn $ unlines [show verdict, name state]
    putStrLn l
