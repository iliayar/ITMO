module Data where

import Helpers

data File = File Expr [Expr]
  deriving (Eq)

data Pred = Pred String | PredEq Term Term
  deriving (Eq, Ord)

data Term = Plus Term Term
          | Times Term Term
          | TermVar Var
          | Succ Term
          | Zero
            deriving (Eq, Ord)

newtype Var = Var String
  deriving (Eq, Ord)

data Expr = Impl Expr Expr
          | Or Expr Expr
          | And Expr Expr
          | Not Expr
          | Forall Var Expr
          | Exists Var Expr
          | ExprPred Pred
          deriving (Eq, Ord)

instance Show File where
  show (File e es) = "|-" ++ show e ++ "\n" ++ unlines (map show es)

instance Show Pred where
  show (Pred p) = p
  show (PredEq l r) = braced $ show l ++ "=" ++ show r

instance Show Term where
  show (Plus l r) = braced $ show l ++ "+" ++ show r
  show (Times l r) = braced $ show l ++ "*" ++ show r
  show (TermVar v) = show v
  show (Succ t) = show t ++ "'"
  show Zero = "0"

instance Show Var where
  show (Var s) = s

instance Show Expr where
  show (Impl l r) = braced $ show l ++ "->" ++ show r
  show (Or l r) = braced $ show l ++ "|" ++ show r
  show (And l r) = braced $ show l ++ "&" ++ show r
  show (Not e) = braced $ "!" ++ show e
  show (Forall v e) = braced $ "@" ++ show v ++ "." ++ show e
  show (Exists v e) = braced $ "?" ++ show v ++ "." ++ show e
  show (ExprPred p) = show p
