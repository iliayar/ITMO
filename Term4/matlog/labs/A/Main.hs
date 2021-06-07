module Main where
import Grammar
import Tokens
import Data

instance Show Expr where
  show (And l r) = "(&," ++ show l ++ "," ++ show r ++ ")"
  show (Or l r) = "(|," ++ show l ++ "," ++ show r ++ ")"
  show (Impl l r) = "(->," ++ show l ++ "," ++ show r ++ ")"
  show (Not e) = "(!" ++ show e ++ ")"
  show (Var v) = v
  


main :: IO ()
main = do
    s <- getContents
    let tokens = scanTokens s
        ast = parseExpr (scanTokens s)
    -- print tokens
    print ast
    
