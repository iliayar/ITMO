{-# LANGUAGE StandaloneDeriving #-}
module Proof where

import Control.Monad.State
import Data.List (intercalate)

newtype Var = Var String
newtype TypeVar = TypeVar String
newtype Rule = Rule Int

instance Show TypeVar where
  show (TypeVar v) = v

instance Show Var where
  show (Var v) = v

instance Show Rule where
  show (Rule r) = "[rule #" ++ show r ++ "]"

data Tree a = Tree a [Tree a]

instance (Show a) => Show (Tree a) where
  show = show' 0
    where
      show' :: Show a => Int -> Tree a -> String
      show' level (Tree v childs) = join (replicate level "*   ") ++ show v ++ "\n" ++
        join (map (show' $ level + 1) childs)

type Proof = Tree Statement

data Statement = Statement Context TypedExpression Rule

instance Show Statement where
  show (Statement ctx expr rule) = show ctx ++ " |- " ++ show expr ++ " " ++ show rule

newtype Context = Context [ContextVar]

instance Show Context where
  show (Context l) = show l

infix 6 :::

data ContextVar = (:::) Var Type

instance Show ContextVar where
  show (v ::: t) = show v ++ " : " ++ show t

infix 6 ::::

data TypedExpression = (::::) Expression Type

instance Show TypedExpression where
  show (e :::: t) = show e ++ " : " ++ show t

data Type = TypeMonoType MonoType
          | TypeForall TypeVar Type

instance Show Type where
  show (TypeMonoType mt) = show mt
  show (TypeForall v t) = paren $ "∀" ++ show v ++ ". " ++ show t

infixr 6 :->:

data MonoType = MonoTypeVar TypeVar
              | (:->:) MonoType MonoType

instance Show MonoType where
  show (MonoTypeVar v) = show v
  show (l :->: r) = paren $ show l ++ " → " ++ show r


infixl 4 :@:
infixr 6 :\:

data Expression = (:\:) Var Expression
                | ExpressionLetIn Var Expression Expression
                | (:@:) Expression Expression
                | ExpressionVar Var

instance Show Expression where
  show (v :\: e) = paren $ "λ" ++ show v ++ ". " ++ show e
  show (ExpressionLetIn v ve e) = paren $ "let " ++ show v ++ " = " ++ show ve ++ " in " ++ show e
  show (l :@: r) = paren $ show l ++ " " ++ show r
  show (ExpressionVar v) = show v

makeTree :: [(Int, a)] -> Tree a
makeTree = head . evalState (makeTree' 0)
  where
    makeTree' :: Int -> State [(Int, a)] [Tree a]
    makeTree' level = do
      l <- get
      case l of
        [] -> return []
        ((lx, vx):xs)
          | lx == level -> do
              put xs
              childs <- makeTree' $ level + 1
              rest <- makeTree' level
              return $ Tree vx childs : rest
          | lx < level -> return []
          | otherwise -> error "unreachable"

paren :: String -> String
paren = ("(" ++) . (++ ")")
