module Natural where

import qualified Proof
import qualified ProofChecker

import Data.List (intercalate)

data Expression = And Expression Expression
                | Or Expression Expression
                | Impl Expression Expression
                | Var String
                | Bottom
    deriving (Eq)
instance Show Expression where
    -- show (Impl e1 e2) = "(" ++ (show e1) ++ " → " ++ (show e2) ++ ")"
    -- show (And e1 e2) = "(" ++ (show e1) ++ " & " ++ (show e2) ++ ")"
    -- show (Or e1 e2) = "(" ++ (show e1) ++ " ∨ " ++ (show e2) ++ ")"
    -- show Bottom = "⟂"
    -- show (Var v) = v
------------------------------------------------
----------- NON PRETTY SYMBOLS -----------------
------------------------------------------------
    show (Impl e1 e2) = "(" ++ (show e1) ++ " -> " ++ (show e2) ++ ")"
    show (And e1 e2) = "(" ++ (show e1) ++ " & " ++ (show e2) ++ ")"
    show (Or e1 e2) = "(" ++ (show e1) ++ " | " ++ (show e2) ++ ")"
    show Bottom = "_|_"
    show (Var v) = v

convertExpression :: Proof.Expression -> Expression
convertExpression (Proof.And l r) = And (convertExpression l) (convertExpression r)
convertExpression (Proof.Or l r) = Or (convertExpression l) (convertExpression r)
convertExpression (Proof.Impl l r) = Impl (convertExpression l) (convertExpression r)
convertExpression (Proof.Var s) = Var s
convertExpression (Proof.Not e) = Impl (convertExpression e) Bottom

convertExpressionRev :: Expression -> Proof.Expression
convertExpressionRev (And l r) = Proof.And (convertExpressionRev l) (convertExpressionRev r)
convertExpressionRev (Or l r) = Proof.Or (convertExpressionRev l) (convertExpressionRev r)
convertExpressionRev (Impl e Bottom) = Proof.Not $ convertExpressionRev e
convertExpressionRev (Impl l r) = Proof.Impl (convertExpressionRev l) (convertExpressionRev r)
convertExpressionRev (Var s) = Proof.Var s

type Statement = ([Expression], Expression)

data Rule = 
    Axiom
    | ImplAdd Node | ImplDel Node Node
    | AndAdd Node Node | AndDelLeft Node | AndDelRight Node
    | OrAddLeft Node | OrAddRight Node | OrDel Node Node Node
    | BottomDel Node
    | Error Node
type Node = (Statement, Rule)

showStatement :: Statement -> String
showStatement (hypos, expr) = (intercalate "," $ map show hypos) ++ " |- " ++ show expr

showTree :: Node -> String
showTree n = unlines $ reverse $ toList 0 n
    where
        toList :: Int -> Node -> [String]
        toList d (st, Axiom) = ["[" ++ (show d) ++ "] " ++ (showStatement st) ++ " [Ax]"]
        toList d (st, ImplDel n1 n2) = showNode d st [n1, n2] "E->"
        toList d (st, ImplAdd n) = showNode d st [n] "I->"
        toList d (st, AndAdd n1 n2) = showNode d st [n1, n2] "I&"
        toList d (st, AndDelLeft n) = showNode d st [n] "Er&"
        toList d (st, AndDelRight n) = showNode d st [n] "El&"
        toList d (st, OrAddLeft n) = showNode d st [n] "Il|"
        toList d (st, OrAddRight n) = showNode d st [n] "Ir|"
        toList d (st, OrDel n1 n2 n3) = showNode d st [n1, n2, n3] "E|"
        toList d (st, BottomDel n) = showNode d st [n] "E_|_"
        toList d (st, Error n) = showNode (d - 1) st [n] "ERROR"
        showNode d st ns mark = ("[" ++ (show d) ++ "] " ++ (showStatement st) ++ " [" ++ mark ++ "]"):(foldl1 (++) $ map (toList $ d + 1) $ reverse ns)

makeAxiom :: Statement -> Node
makeAxiom s@(hypos, e) = if e `elem` hypos then (s, Axiom) else (s, Error (s, Axiom))
-- makeAxiom s@(hypos, e) = if e `elem` hypos then (s, Axiom) else undefined

makeImplAdd :: (Statement -> Node) -> Statement -> Node
makeImplAdd maker s@(hypos, e@(Impl phi psi)) = if e `elem` hypos then (s, Axiom) else (s, ImplAdd $ maker (phi:hypos, psi))

makeImplDel :: Expression -> (Statement -> Node) -> (Statement -> Node) -> Statement -> Node
makeImplDel phi maker1 maker2 s@(hypos, psi) = if psi `elem` hypos then (s, Axiom) else (s, ImplDel (maker1 (hypos, Impl phi psi)) (maker2 (hypos, phi)))

makeAndAdd :: (Statement -> Node) -> (Statement -> Node) -> Statement -> Node
makeAndAdd maker1 maker2 s@(hypos, e@(And phi psi)) = if e `elem` hypos then (s, Axiom) else (s, AndAdd (maker1 (hypos, phi)) (maker2 (hypos, psi)))

makeAndDelLeft :: Expression -> (Statement -> Node) -> Statement -> Node
makeAndDelLeft psi maker s@(hypos, phi) = if phi `elem` hypos then (s, Axiom) else (s, AndDelLeft $ maker (hypos, And psi phi))

makeAndDelRight :: Expression -> (Statement -> Node) -> Statement -> Node
makeAndDelRight phi maker s@(hypos, psi) = if psi `elem` hypos then (s, Axiom) else (s, AndDelRight $ maker (hypos, And psi phi))

makeOrAddLeft :: (Statement -> Node) -> Statement -> Node
makeOrAddLeft maker s@(hypos, e@(Or phi psi)) = if e `elem` hypos then (s, Axiom) else (s, OrAddLeft $ maker (hypos, phi))

makeOrAddRight :: (Statement -> Node) -> Statement -> Node
makeOrAddRight maker s@(hypos, e@(Or phi psi)) = if e `elem` hypos then (s, Axiom) else (s, OrAddRight $ maker (hypos, psi))

makeOrDel :: Expression -> Expression -> (Statement -> Node) -> (Statement -> Node) -> (Statement -> Node) -> Statement -> Node
makeOrDel phi psi maker1 maker2 maker3 s@(hypos, rho) = if rho `elem` hypos then (s, Axiom) else (s, OrDel (maker1 (phi:hypos, rho)) (maker2 (psi:hypos, rho)) (maker3 (hypos, Or phi psi)))

makeBottomDel :: (Statement -> Node) -> Statement -> Node
makeBottomDel maker s@(hypos, phi) = if phi `elem` hypos then (s, Axiom) else (s, BottomDel $ maker (hypos, Bottom))

---------------------------------------------
----------- WITHOUT SIMPLIFING --------------
---------------------------------------------

-- makeImplAdd :: (Statement -> Node) -> Statement -> Node
-- makeImplAdd maker s@(hypos, e@(Impl phi psi)) = (s, ImplAdd $ maker (phi:hypos, psi))

-- makeImplDel :: Expression -> (Statement -> Node) -> (Statement -> Node) -> Statement -> Node
-- makeImplDel phi maker1 maker2 s@(hypos, psi) = (s, ImplDel (maker1 (hypos, Impl phi psi)) (maker2 (hypos, phi)))

-- makeAndAdd :: (Statement -> Node) -> (Statement -> Node) -> Statement -> Node
-- makeAndAdd maker1 maker2 s@(hypos, e@(And phi psi)) = (s, AndAdd (maker1 (hypos, phi)) (maker2 (hypos, psi)))

-- makeAndDelLeft :: Expression -> (Statement -> Node) -> Statement -> Node
-- makeAndDelLeft psi maker s@(hypos, phi) = (s, AndDelLeft $ maker (hypos, And phi psi))

-- makeAndDelRight :: Expression -> (Statement -> Node) -> Statement -> Node
-- makeAndDelRight phi maker s@(hypos, psi) = (s, AndDelRight $ maker (hypos, And phi psi))

-- makeOrAddLeft :: (Statement -> Node) -> Statement -> Node
-- makeOrAddLeft maker s@(hypos, e@(Or phi psi)) = (s, OrAddLeft $ maker (hypos, phi))

-- makeOrAddRight :: (Statement -> Node) -> Statement -> Node
-- makeOrAddRight maker s@(hypos, e@(Or phi psi)) = (s, OrAddRight $ maker (hypos, psi))

-- makeOrDel :: Expression -> Expression -> (Statement -> Node) -> (Statement -> Node) -> (Statement -> Node) -> Statement -> Node
-- makeOrDel phi psi maker1 maker2 maker3 s@(hypos, rho) = (s, OrDel (maker1 (phi:hypos, rho)) (maker2 (psi:hypos, rho)) (maker3 (hypos, Or phi psi)))

-- makeBottomDel :: (Statement -> Node) -> Statement -> Node
-- makeBottomDel maker s@(hypos, phi) = (s, BottomDel $ maker (hypos, Bottom))

axioms :: [(Statement -> Node)]
axioms = 
    [ makeAxiom1
    , makeAxiom2
    , makeAxiom3
    , makeAxiom4
    , makeAxiom5
    , makeAxiom6
    , makeAxiom7
    , makeAxiom8
    , makeAxiom9
    , makeAxiom10 ]
makeAxiom1 = makeImplAdd $ makeImplAdd makeAxiom
makeAxiom2 s@(hypos, e) = 
    let (alpha, beta, _) = matchAxioms3 ProofChecker.matchAxiom2 e
    in makeImplAdd
        (makeImplAdd $ 
            makeImplAdd $ 
                makeImplDel beta 
                    (makeImplDel alpha makeAxiom makeAxiom) 
                    (makeImplDel alpha makeAxiom makeAxiom)) s 
makeAxiom3 = makeImplAdd $ makeImplAdd $ makeAndAdd makeAxiom makeAxiom 
makeAxiom4 s@(hypos, e) =
    let (alpha, beta) = matchAxioms2 ProofChecker.matchAxiom4 e
    in makeImplAdd (makeAndDelRight beta makeAxiom) s
makeAxiom5 s@(hypos, e) =
    let (alpha, beta) = matchAxioms2 ProofChecker.matchAxiom5 e
    in makeImplAdd (makeAndDelLeft alpha makeAxiom) s
makeAxiom6 = makeImplAdd $ makeOrAddLeft makeAxiom
makeAxiom7 = makeImplAdd $ makeOrAddRight makeAxiom
makeAxiom8 s@(hypos, e) =
    let (alpha, beta, gamma) = matchAxioms3 ProofChecker.matchAxiom8 e
    in makeImplAdd
        (makeImplAdd $ makeImplAdd $
            makeOrDel alpha beta
                (makeImplDel alpha makeAxiom makeAxiom)
                (makeImplDel beta makeAxiom makeAxiom)
                makeAxiom) s
makeAxiom9 s@(hypos, e) =
    let (alpha, beta) = matchAxioms2 ProofChecker.matchAxiom9 e
    in makeImplAdd
        (makeImplAdd $ makeImplAdd $
            makeImplDel beta
                (makeImplDel alpha makeAxiom makeAxiom)
                (makeImplDel alpha makeAxiom makeAxiom)) s
makeAxiom10 s@(hypos, e) =
    let (alpha, beta) = matchAxioms2 ProofChecker.matchAxiom10 e
    in makeImplAdd
        (makeImplAdd $
            makeBottomDel $
                makeImplDel alpha makeAxiom makeAxiom) s

matchAxioms2 :: (Proof.Expression -> Maybe (Proof.Expression, Proof.Expression)) -> Expression -> (Expression, Expression)
matchAxioms2 f e = let Just (e1, e2) = f $ convertExpressionRev e in (convertExpression e1, convertExpression e2)

matchAxioms3 :: (Proof.Expression -> Maybe (Proof.Expression, Proof.Expression, Proof.Expression)) -> Expression -> (Expression, Expression, Expression)
matchAxioms3 f e = let Just (e1, e2, e3) = f $ convertExpressionRev e in (convertExpression e1, convertExpression e2, convertExpression e3)

