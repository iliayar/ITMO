module Proof where

data File =  File Context Expression [Expression]
    deriving (Eq)
instance Show File where
    show (File ctx expr ls) = (show ctx) ++ " |- " ++ (show expr) ++ "\n" ++ (unlines $ map show ls)
data Context = Context [Expression] 
             | EmptyContext
    deriving (Show, Eq)
data Expression = And Expression Expression
                | Or Expression Expression
                | Impl Expression Expression
                | Not Expression
                | Var String
    deriving (Eq)
instance Show Expression where
    show (Impl e1 e2) = "(->," ++ (show e1) ++ "," ++ (show e2) ++ ")"
    show (And e1 e2) = "(&," ++ (show e1) ++ "," ++ (show e2) ++ ")"
    show (Or e1 e2) = "(|," ++ (show e1) ++ "," ++ (show e2) ++ ")"
    show (Not e1) = "(!" ++ (show e1) ++ ")"
    show (Var v) = v

contextToExpressions :: Context -> [Expression]
contextToExpressions (Context es) = es
contextToExpressions EmptyContext = []

