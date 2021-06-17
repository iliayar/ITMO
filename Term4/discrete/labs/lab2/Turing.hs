{-# LANGUAGE TupleSections #-}
module Turing where

import Data.Maybe

charset :: String
--charset = map toEnum [0..255]
charset = "0123456789-_+*^$#<>()"

data Move = R | L | T
data State = State { name :: String, transitions :: Char -> Maybe (State, Char, Move) }

instance Eq State where
  st1 == st2 = name st1 == name st2

instance Show Move where
    show R = ">"
    show L = "<"
    show T = "^"

instance Show State where
    show State
        { name = nm
        , transitions=transitions }
        = unlines $ map (showTransition nm) $ mapMaybe (\c -> (c,) <$> transitions c) charset
            where showTransition nm (ch, (st, c, m)) = nm ++ " " ++ [ch] ++ " -> " ++ name st ++ " " ++ [c] ++ " " ++ show m

data Machine = Machine { states :: [State], start :: State, accept :: State, reject :: State, blank :: Char }

instance Show Machine where
    show m = unlines $
        [ "start: " ++ name (start m)
        , "accept: " ++ name (accept m)
        , "reject: " ++ name (reject m)
        , "blank: " ++ [blank m]]
        ++ map show (states m)

stateFromFunc :: String -> (Char -> (State, Char, Move)) -> State
stateFromFunc s f = State { name  = s, transitions = Just . f }

stateFromList :: String -> [(Char, State, Char, Move)] -> State
stateFromList n ts = State { name = n,
            transitions = transitions' }
    where
        transitions' ch = findTransition ch ts
        findTransition ch ((c, s, nc, m):xs) = if c == ch then Just (s, nc, m) else findTransition ch xs
        findTransition _ [] = Nothing

data Logger a = Logger a String

instance Monad Logger where
    return v = Logger v ""
    (Logger v1 l1) >>= f
        = let (Logger v2 l2) = f v1
            in Logger v2 (l1 ++ l2)
instance Functor Logger
instance Applicative Logger

data Verdict = Accept | Reject
instance Show Verdict where
    show Accept = "accept"
    show Reject = "reject"

logStr :: String -> Logger ()
logStr = Logger ()

logStrLn :: String -> Logger ()
logStrLn = logStr . (++"\n")

data MachineState = MachineState { pos :: Int, string :: String, state :: State }

-- runMachineDefault = runMachine 10000000 500
runMachineDefault = runMachine 200 500

runMachine :: Int -> Int -> String -> Machine -> Logger (Either String (Verdict, State))
runMachine stepsLimit statesLimit string machine
    = if statesLimit < length (states machine)
        then return $ Left "Too many states"
        else machineStep stepsLimit 0 machine (MachineState { pos = 0, string = string, state = start machine})

machineStep :: Int -> Int -> Machine -> MachineState -> Logger (Either String (Verdict, State))
machineStep stepsLimit steps machine MachineState { pos = p, string = s, state = st}
    = do
        logStrLn (name st)
        logStrLn s
        logStrLn $ replicate p ' ' ++ "^"
        if stepsLimit < steps
            then return $ Left "Steps limit"
            else case transitions st (s !! p) of
                    Nothing -> do
                      logStrLn s
                      logStrLn $ replicate p ' ' ++ "^"
                      return $ if st == accept machine then Right (Accept, st) else Right (Reject, st)
                    Just (ns, ch, m) ->
                        let str = updateString 0 p ch s
                        in case m of
                            R -> let (np, nstring) = updatePos (p + 1) str (blank machine)
                                    in machineStep stepsLimit (steps + 1) machine $ MachineState { pos = np, string = nstring, state = ns}
                            L -> let (np, nstring) = updatePos (p - 1) str (blank machine)
                                    in machineStep stepsLimit (steps + 1) machine $ MachineState { pos = np, string = nstring, state = ns}
                            T -> let (np, nstring) = updatePos p str (blank machine)
                                    in machineStep stepsLimit (steps + 1) machine $ MachineState { pos = np, string = nstring, state = ns}
    where
        updatePos np s blank
            | np < 0 = (0, blank:s)
            | np < length s = (np, s)
            | otherwise = (np, s ++ [blank])
        updateString i p ch (c:s) = if p == i then ch:s else c:updateString (i + 1) p ch s

