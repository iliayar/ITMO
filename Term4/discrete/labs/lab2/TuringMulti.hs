{-# LANGUAGE TupleSections #-}
module TuringMulti where

import Data.Maybe
import Data.List

charset :: [String]
--charset = map toEnum [0..255]
charset = ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "-", "_", "+", "*", "^", "$", "#", "<", ">", "(", ")", "r0", "r1", "l0", "l1", "f0", "f1", "t0", "t1", "|"]
ntapes = 2

data Move = R | L | T
data State = State { name :: String, transitions :: [String] -> Maybe (State, [(String, Move)]) }

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
        = unlines $ map (showTransition nm) $ mapMaybe (\c -> (c,) <$> transitions c) $ genCharsets ntapes
            where showTransition nm (chs, (st, ts)) = nm ++ " " ++ unwords chs ++ " -> " ++ name st ++ " " ++ unwords (map (\(c, m) -> c ++ " " ++ show m) ts)
                  genCharsets 1 = map (:[]) charset
                  genCharsets n = [x:xs | x <- charset, xs <- genCharsets (n - 1) ]

data Machine = Machine { states :: [State], start :: State, accept :: State, reject :: State, blank :: String }

instance Show Machine where
    show m = unlines $
        [ show ntapes
        -- , "start: " ++ name (start m)
        -- , "accept: " ++ name (accept m)
        -- , "reject: " ++ name (reject m)
        -- , "blank: " ++ blank m
        ] ++ map show (states m)

stateFromFunc :: String -> ([String] -> (State, [(String, Move)])) -> State
stateFromFunc s f = State { name  = s, transitions = Just . f }

stateFromList :: String -> [([String], State, [(String, Move)])] -> State
stateFromList n ts = State { name = n,
            transitions = transitions' }
    where
        transitions' ch = findTransition ch ts
        findTransition ch ((c, s, ts):xs) = if map fst ts == ch then Just (s, ts) else findTransition ch xs
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

data MachineState = MachineState { pos :: [Int], string :: [[String]], state :: State }

runMachineDefault = runMachine 10000000 500
-- runMachineDefault = runMachine 500 500

runMachine :: Int -> Int -> [[String]] -> Machine -> Logger (Either String (Verdict, State))
runMachine stepsLimit statesLimit string machine
    = if statesLimit < length (states machine)
        then return $ Left "Too many states"
        else machineStep stepsLimit 0 machine (MachineState { pos = replicate ntapes 0, string = string, state = start machine})

machineStep :: Int -> Int -> Machine -> MachineState -> Logger (Either String (Verdict, State))
machineStep stepsLimit steps machine MachineState { pos = ps, string = ss, state = st}
    = do
        logStrLn $ name st
        mapM_
          (\ (s, p) -> do
              logStrLn $ unwords s
              logStrLn $ replicate ((+(-1)) $ length $ unwords $ take (p + 1) s) ' ' ++ "^"
          ) $ zip ss ps
        if stepsLimit < steps
            then return $ Left "Steps limit"
            else case transitions st (zipWith (!!) ss ps) of
                    Nothing -> do
                      -- mapM_
                      --   ( \(s, p) -> do
                      --       logStrLn $ unwords s
                      --       logStrLn $ replicate ((+ (-1)) $ length $ unwords $ take (p + 1) s) ' ' ++ "^"
                      --   ) $ zip ss ps
                      return $ if st == accept machine then Right (Accept, st) else Right (Reject, st)
                    Just (ns, ts) ->
                        let strs = zipWith (\ (s, p) ch -> updateString s p ch) (zip ss ps) $ map fst ts
                            ndata = zipWith (\ str p -> updatePos p str (blank machine)) strs $ zipWith getPos (map snd ts) ps
                        in machineStep stepsLimit (steps + 1) machine $ MachineState { pos = map fst ndata, string = map snd ndata, state = ns}
    where
        getPos :: Move -> Int -> Int
        getPos R = (+1)
        getPos L = (+(-1))
        getPos T = id
        updatePos :: Int -> [String] -> String -> (Int, [String])
        updatePos np s blank
            | np < 0 = (0, blank:s)
            | np < length s = (np, s)
            | otherwise = (np, s ++ [blank])
        updateString :: [String] -> Int -> String -> [String]
        updateString (c:s) 0 ch = ch:s
        updateString (c:s) p ch = c:updateString s (p - 1) ch

