{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE TypeSynonymInstances      #-}

module HW3.Evaluator.Base
  ( HiExcept
  , BinaryFunction(..)
  , UnaryFunction(..)
  , Function(..)
  , RawFunction(..)
  , evalFunc ) where

import Control.Monad.Trans.Except (ExceptT, throwE)
import HW3.Base

type HiExcept m = ExceptT HiError m

-- | Existential type represents an entity that can be calculated from
-- `HiValue` to `HiValue`, with native 2 argument function
data BinaryFunction m = forall a b r. BinaryFunction
   { extract1BF :: HiValue -> Maybe a -- ^ Extracts native type from `HiValue` as 1st argument
   , extract2BF :: HiValue -> Maybe b -- ^ Extracts native type from `HiValue` as 2nd argument
   , ctrBF      :: r -> HiValue -- ^ Extracts native type from `HiValue` as 3rd argument
   , evalBF     :: a -> b -> HiExcept m r -- ^ Evaluates function, may throw exception and perform actions
   }

-- | Existential type represents an entity that can be calculated from
-- `HiValue` to `HiValue`, with native 1 argument function
data UnaryFunction m = forall a r. UnaryFunction
   { extractUF :: HiValue -> Maybe a -- ^ Extracts native type from `HiValue`
   , ctrUF     :: r -> HiValue -- ^ Constucts `HiValue` from native type
   , evalUF    :: a -> HiExcept m r -- ^ Evaluates function, may throw exception and perform actions
   }

-- | Evaluates unary function, before checks arity and arguments
-- types. Throws `HiErrorArityMismatch` if number of arguments is not
-- 1, `HiErrorInvalidArgument` if extracted `Nothing` from argument
evalUnaryFunction :: Monad m => UnaryFunction m -> [HiValue] -> HiExcept m HiValue
evalUnaryFunction UnaryFunction { .. } [v] =
  case extractUF v of
    Just arg -> ctrUF <$> evalUF arg
    _        -> throwE HiErrorInvalidArgument
evalUnaryFunction _ _ = throwE HiErrorArityMismatch

-- | Evaluates binary function, before checks arity and arguments
-- types. Throws `HiErrorArityMismatch` if number of arguments is not
-- 2, `HiErrorInvalidArgument` if extracted `Nothing` from any
-- argument
evalBinaryFunction :: Monad m => BinaryFunction m -> [HiValue] -> HiExcept m HiValue
evalBinaryFunction BinaryFunction { .. } [v1, v2] =
  case (extract1BF v1, extract2BF v2) of
    (Just arg1, Just arg2) -> ctrBF <$> evalBF arg1 arg2
    _                      -> throwE HiErrorInvalidArgument
evalBinaryFunction _ _ = throwE HiErrorArityMismatch

newtype RawFunction m = RawFunction ([HiValue] -> HiExcept m HiValue)

-- | Union of functions with different arity
data Function m = FunctionUnary (UnaryFunction m)
                | FunctionBinary (BinaryFunction m)
                | FunctionRaw (RawFunction m)

-- | Evaluates function, checks arity and types for unary and binary functions
evalFunc :: Monad m => Function m -> [HiValue] -> HiExcept m HiValue
evalFunc (FunctionRaw (RawFunction f)) = f
evalFunc (FunctionUnary f)             = evalUnaryFunction f
evalFunc (FunctionBinary f)            = evalBinaryFunction f
