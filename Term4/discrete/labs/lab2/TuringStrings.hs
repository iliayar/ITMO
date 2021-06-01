{-# LANGUAGE TupleSections #-}
module TuringStrings where

import Data.Maybe
import Data.List

charset :: [String]
--charset = map toEnum [0..255]
charset = ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "-", "_", "+", "*", "^", "$", "#", "<", ">", "(", ")", "r0", "r1", "l0", "l1", "f0", "f1", "t0", "t1", "|", "a", "o"]

data Move = R | L | T
data State = State { name :: String, transitions :: String -> Maybe (State, String, Move) }

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
            where showTransition nm (ch, (st, c, m)) = nm ++ " " ++ ch ++ " -> " ++ name st ++ " " ++ c ++ " " ++ show m

data Machine = Machine { states :: [State], start :: State, accept :: State, reject :: State, blank :: String }

instance Show Machine where
    show m = unlines $
        [ "start: " ++ name (start m)
        , "accept: " ++ name (accept m)
        , "reject: " ++ name (reject m)
        , "blank: " ++ blank m]
        ++ map show (states m)

stateFromFunc :: String -> (String -> (State, String, Move)) -> State
stateFromFunc s f = State { name  = s, transitions = Just . f }

stateFromList :: String -> [(String, State, String, Move)] -> State
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

data MachineState = MachineState { pos :: Int, string :: [String], state :: State }

runMachineDefault = runMachine 10000000 500
-- runMachineDefault = runMachine 500 500

runMachine :: Int -> Int -> [String] -> Machine -> Logger (Either String (Verdict, State))
runMachine stepsLimit statesLimit string machine
    = if statesLimit < length (states machine)
        then return $ Left "Too many states"
        else machineStep stepsLimit 0 machine (MachineState { pos = 0, string = string, state = start machine})

machineStep :: Int -> Int -> Machine -> MachineState -> Logger (Either String (Verdict, State))
machineStep stepsLimit steps machine MachineState { pos = p, string = s, state = st}
    = do
        -- logStrLn $ name st
        -- logStrLn $ intercalate " " s
        -- logStrLn $ replicate ((+(-1)) $ length $ intercalate " " $ take (p + 1) s) ' ' ++ "^"
        -- logStrLn $ intercalate " " $ take (p + 1) s
        if stepsLimit < steps
            then return $ Left "Steps limit"
            else case transitions st (s !! p) of
                    Nothing -> do
                      logStrLn $ intercalate " " s
                      logStrLn $ replicate ((+(-1)) $ length $ intercalate " " $ take (p + 1) s) ' ' ++ "^"
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

