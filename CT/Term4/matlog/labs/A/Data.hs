module Data where

data Expr = Impl Expr Expr
          | Or Expr Expr
          | And Expr Expr
          | Not Expr
          | Var String
