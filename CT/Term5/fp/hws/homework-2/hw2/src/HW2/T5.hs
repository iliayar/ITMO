module HW2.T5
  ( eval
  , mapExceptState
  , wrapExceptState
  , joinExceptState
  , modifyExceptState
  , throwExceptState
  , ExceptState(..)
  , EvaluationError(..) ) where

import qualified Control.Monad
import HW2.T1 (Annotated (..), Except (..))
import HW2.T4 (Expr (..), Prim (..))

-- |Data type that mostly used as Monad that can modify its state and
-- can contain computation error
data ExceptState e s a = ES { runES :: s -> Except e (Annotated s a) }

-- |Apply a function to a value if it is not failure keeping the state
-- unmodified
mapExceptState :: (a -> b) -> ExceptState e s a -> ExceptState e s b
mapExceptState f state = ES $
  \s -> case runES state s of
    Error e               -> Error e
    Success (a :# sInner) -> Success (f a :# sInner)

-- |Make an state with provided value and empty state
wrapExceptState :: a -> ExceptState e s a
wrapExceptState a = ES $ \s -> Success (a :# s)

-- |Run two consequent computation. Result in value only if no one
-- computation failed.
joinExceptState :: ExceptState e s (ExceptState e s a) -> ExceptState e s a
joinExceptState state = ES $
  \s -> case runES state s of
    Error e                        -> Error e
    Success (stateInner :# sInner) -> runES stateInner sInner

-- |Apply a function to current state
modifyExceptState :: (s -> s) -> ExceptState e s ()
modifyExceptState f = ES $ \s -> Success (() :# f s)

-- |Force a computation to fail
throwExceptState :: e -> ExceptState e s a
throwExceptState e = ES $ \_ -> Error e

instance Functor (ExceptState e s) where
  fmap = mapExceptState

instance Applicative (ExceptState e s) where
  pure = wrapExceptState
  a <*> b = Control.Monad.ap a b

instance Monad (ExceptState e s) where
  a >>= b = joinExceptState (fmap b a)

-- |Data type represents a kind of computation error
data EvaluationError
  = DivideByZero -- ^ Division by zero occured

-- |Evaluates expression. Returns its value and list of all operaion
-- performed during computation only if no error occured
eval :: Expr -> ExceptState EvaluationError [Prim Double] Double
eval = eval'
  where
    evalOp2Validate' :: (Double -> Double -> ExceptState EvaluationError [Prim Double] ())
                     -> (Double -> Double -> Double)
                     -> (Double -> Double -> Prim Double)
                     -> Expr -> Expr -> ExceptState EvaluationError [Prim Double] Double
    evalOp2Validate' validate f g x y = do
      xVal <- eval x
      yVal <- eval y
      validate xVal yVal
      modifyExceptState (g xVal yVal:)
      pure $ f xVal yVal

    evalOp2' :: (Double -> Double -> Double)
             -> (Double -> Double -> Prim Double)
             -> Expr -> Expr -> ExceptState EvaluationError [Prim Double] Double
    evalOp2' = evalOp2Validate' $ \_ _ -> pure ()

    evalOp1' :: (Double -> Double)
             -> (Double -> Prim Double)
             -> Expr -> ExceptState EvaluationError [Prim Double] Double
    evalOp1' f g x = do
      xVal <- eval x
      modifyExceptState (g xVal:)
      pure $ f xVal

    eval' :: Expr -> ExceptState EvaluationError [Prim Double] Double
    eval' (Val x) = pure x
    eval' (Op (Add x y)) = evalOp2' (+) Add x y
    eval' (Op (Sub x y)) = evalOp2' (-) Sub x y
    eval' (Op (Mul x y)) = evalOp2' (*) Mul x y
    eval' (Op (Div x y)) = evalOp2Validate'
      ( \_ b ->
          if b == 0
          then throwExceptState DivideByZero
          else pure () ) (/) Div x y
    eval' (Op (Abs x)) = evalOp1' abs Abs x
    eval' (Op (Sgn x)) = evalOp1' signum Sgn x
