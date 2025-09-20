{-# OPTIONS_GHC -fno-warn-orphans #-}

module HW3.Evaluator.FunctionHelpers
  ( mkUnaryFunctionBool
  , mkBinaryFunctionRatNoExcept
  , mkBinaryFunctionRat
  , mkBinaryFunctionStringNoExcept
  , mkUnaryFunctionStringNoExcept'
  , mkUnaryFunctionStringNoExcept
  , mkUnaryFunctionListNoExcept'
  , mkUnaryFunctionListNoExcept
  , mkUnaryFunctionBytesNoExcept'
  , mkUnaryFunctionBytesNoExcept
  , rawFunction
  , mkOverloadedFunction
  , unaryFunctionNoExcept
  , unaryFunction
  , binaryFunctionNoExcept
  , binaryFunction ) where

import Control.Monad.Trans.Except (catchE, throwE)
import qualified Data.ByteString as BS
import qualified Data.Sequence as S
import qualified Data.Text as T
import HW3.Base
import HW3.Evaluator.Base
import HW3.Evaluator.Helpers

-- | Constructs `Function` from custom evaluator
rawFunction :: Monad m => ([HiValue] -> HiExcept m HiValue) -> Function m
rawFunction = FunctionRaw . RawFunction

-- | Constructs `Function` with one argument which always
-- succeeds. See `UnaryFunction`
unaryFunctionNoExcept :: Monad m
  => (HiValue -> Maybe a)
  -> (r -> HiValue)
  -> (a -> r)
  -> Function m
unaryFunctionNoExcept ex ctr eval = unaryFunction ex ctr $ \x -> pure $ eval x

-- | Constructs `Function` with one argument which can fail. See
-- `UnaryFunction`
unaryFunction :: Monad m
  => (HiValue -> Maybe a)
  -> (r -> HiValue)
  -> (a -> HiExcept m r)
  -> Function m
unaryFunction ex ctr eval = FunctionUnary $ UnaryFunction
  { extractUF = ex
  , ctrUF = ctr
  , evalUF = eval
  }

-- | Constructs `Function` with two arguments which always
-- succeeds. See `BinaryFunction`
binaryFunctionNoExcept :: Monad m
  => (HiValue -> Maybe a)
  -> (HiValue -> Maybe b)
  -> (r -> HiValue)
  -> (a -> b -> r)
  -> Function m
binaryFunctionNoExcept ex1 ex2 ctr eval = binaryFunction ex1 ex2 ctr $ \x y -> pure $ eval x y

-- | Constructs `Function` with two arguments which can fail. See
-- `BinaryFunction`
binaryFunction :: Monad m
  => (HiValue -> Maybe a)
  -> (HiValue -> Maybe b)
  -> (r -> HiValue)
  -> (a -> b -> HiExcept m r)
  -> Function m
binaryFunction ex1 ex2 ctr eval = FunctionBinary $ BinaryFunction
  { extract1BF = ex1
  , extract2BF = ex2
  , ctrBF = ctr
  , evalBF = eval
  }

-- | Combines multiple functions. The result function tryes to
-- evaluate each function, until one succeed. If no one succeed
-- results in `HiErrorInvalidArgument`
mkOverloadedFunction :: (Monad m) => [Function m] -> Function m
mkOverloadedFunction = rawFunction . tryEvalAny . map evalFunc
  where
    tryEvalAny :: Monad m
      => [[HiValue] -> HiExcept m a]
      -> [HiValue]
      -> HiExcept m a
    tryEvalAny (f:fs) args = do
      let evalNext = tryEvalAny fs args
      catchE (f args) $ \e -> case e of
        HiErrorInvalidArgument -> evalNext
        _                      -> throwE e
    tryEvalAny [] _ = throwE HiErrorInvalidArgument

mkUnaryFunctionBool :: Monad m => (Bool -> Bool) -> Function m
mkUnaryFunctionBool = unaryFunctionNoExcept exBool HiValueBool

mkBinaryFunctionRatNoExcept :: Monad m => (Rational -> Rational -> Rational) -> Function m
mkBinaryFunctionRatNoExcept = binaryFunctionNoExcept exNumber exNumber HiValueNumber

mkBinaryFunctionRat :: Monad m => (Rational -> Rational -> HiExcept m Rational) -> Function m
mkBinaryFunctionRat = binaryFunction exNumber exNumber HiValueNumber

mkBinaryFunctionStringNoExcept :: Monad m => (T.Text -> T.Text -> T.Text) -> Function m
mkBinaryFunctionStringNoExcept = binaryFunctionNoExcept exString exString HiValueString

mkUnaryFunctionStringNoExcept' :: Monad m => (a -> HiValue) -> (T.Text -> a) -> Function m
mkUnaryFunctionStringNoExcept' = unaryFunctionNoExcept exString

mkUnaryFunctionStringNoExcept :: Monad m => (T.Text -> T.Text) -> Function m
mkUnaryFunctionStringNoExcept = mkUnaryFunctionStringNoExcept' HiValueString

mkUnaryFunctionBytesNoExcept' :: Monad m => (a -> HiValue) -> (BS.ByteString -> a) -> Function m
mkUnaryFunctionBytesNoExcept' = unaryFunctionNoExcept exBytes

mkUnaryFunctionBytesNoExcept :: Monad m => (BS.ByteString -> BS.ByteString) -> Function m
mkUnaryFunctionBytesNoExcept = mkUnaryFunctionBytesNoExcept' HiValueBytes

mkUnaryFunctionListNoExcept' :: Monad m => (a -> HiValue) -> (S.Seq HiValue -> a) -> Function m
mkUnaryFunctionListNoExcept' = unaryFunctionNoExcept exList

mkUnaryFunctionListNoExcept :: Monad m => (S.Seq HiValue -> S.Seq HiValue) -> Function m
mkUnaryFunctionListNoExcept = mkUnaryFunctionListNoExcept' HiValueList
