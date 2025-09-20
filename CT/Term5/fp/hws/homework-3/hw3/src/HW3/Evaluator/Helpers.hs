{-# LANGUAGE NamedWildCards      #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}

module HW3.Evaluator.Helpers
  ( evalSlice
  , flipBinaryFunction
  , exNumber
  , exInteger
  , exInt
  , exPosInteger
  , exBool
  , exFunction
  , exList
  , exDict
  , exBytes
  , exString
  , exTime
  , exAny ) where

import Control.Monad.Trans.Except (throwE)
import Data.Bool (bool)
import qualified Data.ByteString as BS
import qualified Data.Map as M
import qualified Data.Sequence as S
import qualified Data.Text as T
import qualified Data.Time as UTC
import HW3.Base
import HW3.Evaluator.Base
import HW3.Helpers

-- | Change the position of arguments for binary function. For others
-- do nothing
flipBinaryFunction :: Monad m => Function m -> Function m
flipBinaryFunction (FunctionBinary BinaryFunction { .. }) = FunctionBinary $ BinaryFunction
  { extract1BF = extract2BF
  , extract2BF = extract1BF
  , ctrBF = ctrBF
  , evalBF = flip evalBF
  }
flipBinaryFunction f = f

-- | Takes slice or element by index of some container.
evalSlice :: forall a b m i. (Monad m, Integral i)
  => (a -> i)      -- ^ Function for obtaining length
  -> (a -> i -> b) -- ^ Function for taking one element by index
  -> (b -> HiValue)  -- ^ Function to convert value into HiValue
  -> (a -> HiValue)  -- ^ Function to convert slice into HiValue
  -> (i -> a -> a) -- ^ Function for taking first `n` elements
  -> (i -> a -> a) -- ^ Function for drop first `n` elements
  -> a -- ^ Container object
  -> [HiValue] -> HiExcept m HiValue
evalSlice lengthF singleF ctr ctrSlice takeF dropF s args =
  let sLength = lengthF s
  in case args of
       [HiValueNumber (ratToInt -> Just n)] -> pure $
         if fromIntegral n >= sLength || n < 0
         then HiValueNull
         else ctr $ singleF s $ fromIntegral n
       [HiValueNumber (ratToInt -> Just begin), HiValueNumber (ratToInt -> Just end)] ->
         pure $ stringSlice sLength (fromIntegral begin) (fromIntegral end) s
       [HiValueNull, HiValueNumber (ratToInt -> Just end)] ->
         pure $ stringSlice sLength 0 (fromIntegral end) s
       [HiValueNumber (ratToInt -> Just begin), HiValueNull] ->
         pure $ stringSlice sLength (fromIntegral begin) sLength s
       [HiValueNull, HiValueNull] ->
         pure $ stringSlice sLength 0 sLength s
       _  -> throwE HiErrorInvalidArgument
    where
      stringSlice :: i -> i -> i -> a -> HiValue
      stringSlice sLength begin end =
        let (nBegin, nEnd) = bounded sLength (begin, end)
        in ctrSlice . takeF (nEnd - nBegin) . dropF nBegin

      bounded :: i -> (i, i) -> (i, i)
      bounded sLength (begin, end) =
        let nBegin = bounded' sLength begin
            nEnd   = bounded' sLength end
        in if nEnd < nBegin
           then (0, 0)
           else (nBegin, nEnd)

      bounded' :: i -> i -> i
      bounded' sLength idx =
        if idx >= 0
        then min sLength idx
        else max 0 (idx + sLength)

exNumber :: HiValue -> Maybe Rational
exNumber (HiValueNumber v) = Just v
exNumber _                 = Nothing

exInteger :: HiValue -> Maybe Integer
exInteger (HiValueNumber v) = ratToInteger v
exInteger _                 = Nothing

exInt :: HiValue -> Maybe Int
exInt (HiValueNumber v) = ratToInt v
exInt _                 = Nothing

exBool :: HiValue -> Maybe Bool
exBool (HiValueBool v) = Just v
exBool _               = Nothing

exFunction :: HiValue -> Maybe HiFun
exFunction (HiValueFunction v) = Just v
exFunction _                   = Nothing

exList :: HiValue -> Maybe (S.Seq HiValue)
exList (HiValueList v) = Just v
exList _               = Nothing

exDict :: HiValue -> Maybe (M.Map HiValue HiValue)
exDict (HiValueDict v) = Just v
exDict _               = Nothing

exBytes :: HiValue -> Maybe BS.ByteString
exBytes (HiValueBytes v) = Just v
exBytes _                = Nothing

exString :: HiValue -> Maybe T.Text
exString (HiValueString v) = Just v
exString _                 = Nothing

exTime :: HiValue -> Maybe UTC.UTCTime
exTime (HiValueTime v) = Just v
exTime _               = Nothing

exAny :: HiValue -> Maybe HiValue
exAny = Just

exPosInteger :: HiValue -> Maybe Integer
exPosInteger (HiValueNumber (ratToInteger -> Just n)) = bool Nothing (Just n) $ n > 0
exPosInteger _                                        = Nothing
