module HW2.T4
 ( eval
 , mapState
 , wrapState
 , joinState
 , modifyState
 , State(..)
 , Prim(..)
 , Expr(..) ) where

import HW2.T1 (Annotated (..), mapAnnotated)

import qualified Control.Monad

-- |Data type that mostly used as Monad that can modify its state
data State s a = S { runS :: s -> Annotated s a}

-- |Apply a function to value stored in state
mapState :: (a -> b) -> State s a -> State s b
mapState f state = S $ \s -> mapAnnotated f $ runS state s

-- |Make an empty state contains provided value
wrapState :: a -> State s a
wrapState a = S $ \s -> a :# s

-- |Runs the sequence of two computations, returning the result of the
-- last
joinState :: State s (State s a) -> State s a
joinState state = S $ \s ->
  case runS state s of
    (stateInner :# sInner) -> runS stateInner sInner

-- |Apply a function to current state
modifyState :: (s -> s) -> State s ()
modifyState f = S $ \s -> () :# f s

instance Functor (State s) where
  fmap = mapState

instance Applicative (State s) where
  pure = wrapState
  p <*> q = Control.Monad.ap p q

instance Monad (State s) where
  m >>= f = joinState (fmap f m)

-- |Data type represents an mathematical operations: binary
-- operations: `+`, `-`, `*`, `/` and unary operations: `abs`, `signum`
data Prim a
  = Add a a -- ^ addition
  | Sub a a -- ^ subtraction
  | Mul a a -- ^ multiplication
  | Div a a -- ^ division
  | Abs a -- ^ absolute value
  | Sgn a -- ^ -1 if the value is negative, 1 if positive and 0 otherwise

-- |Data type represents and mathematical expression with floating
-- point numbers
data Expr
  = Val Double -- ^ Floating point number
  | Op (Prim Expr) -- ^ Operation

instance Num Expr where
  x + y = Op (Add x y)
  x - y = Op (Sub x y)
  x * y = Op (Mul x y)
  abs x = Op (Abs x)
  signum x = Op (Sgn x)

  fromInteger x = Val (fromInteger x)

instance Fractional Expr where
  x / y = Op (Div x y)
  fromRational x = Val (fromRational x)

-- |Evaluates expression. Returns its value and list of all operaion
-- performed during computation
eval :: Expr -> State [Prim Double] Double
eval (Val x) = return x
eval (Op op) = evalOp op
  where
    evalOp2' :: (Double -> Double -> Double) -> (Double -> Double -> Prim Double) -> Expr -> Expr -> State [Prim Double] Double
    evalOp2' f g x y = do
      xVal <- eval x
      yVal <- eval y
      modifyState (g xVal yVal:)
      return $ f xVal yVal

    evalOp1' :: (Double -> Double) -> (Double -> Prim Double) -> Expr -> State [Prim Double] Double
    evalOp1' f g x = do
      xVal <- eval x
      modifyState (g xVal:)
      return $ f xVal

    evalOp :: Prim Expr -> State [Prim Double] Double
    evalOp (Add x y) = evalOp2' (+) Add x y
    evalOp (Sub x y) = evalOp2' (-) Sub x y
    evalOp (Mul x y) = evalOp2' (*) Mul x y
    evalOp (Div x y) = evalOp2' (/) Div x y
    evalOp (Abs x)   = evalOp1' abs Abs x
    evalOp (Sgn x)   = evalOp1' signum Sgn x


