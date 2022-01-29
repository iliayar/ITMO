module Proof where

import Control.Monad.State
import Data.List (intercalate)
import qualified Data.Map as M

newtype Var = Var String
  deriving (Eq, Ord)
newtype TypeVar = TypeVar String
  deriving (Eq, Ord)
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

newtype Context = Context (M.Map Var Type)
  deriving (Eq)

instance Show Context where
  show (Context m) = intercalate ", " $ map (\(v, t) -> show v ++ " : " ++ show t) $ M.toList m

infix 3 :::

data TypedExpression = (:::) Expression Type

instance Show TypedExpression where
  show (e ::: t) = show e ++ " : " ++ show t

data Type = TypeMonoType MonoType
          | TypeForall TypeVar Type
          deriving (Eq)

instance Show Type where
  show (TypeMonoType mt) = show mt
  show (TypeForall v t) = paren $ "∀" ++ show v ++ ". " ++ show t

infixr 6 :->:

data MonoType = MonoTypeVar TypeVar
              | (:->:) MonoType MonoType
          deriving (Eq)

instance Show MonoType where
  show (MonoTypeVar v) = show v
  show (l :->: r) = paren $ show l ++ " → " ++ show r


infixl 4 :@:
infixr 6 :\:

data Expression = (:\:) Var Expression
                | ExpressionLetIn Var Expression Expression
                | (:@:) Expression Expression
                | ExpressionVar Var
                  deriving (Eq)

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
