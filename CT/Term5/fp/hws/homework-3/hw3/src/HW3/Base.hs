{-# LANGUAGE DeriveGeneric #-}

module HW3.Base
  ( HiFun(..)
  , HiValue(..)
  , HiExpr(..)
  , HiError(..)
  , HiAction(..)
  , HiMonad(..) ) where

import Codec.Serialise
import Data.ByteString (ByteString)
import Data.Map (Map)
import Data.Sequence (Seq)
import Data.Text (Text)
import Data.Time (UTCTime)
import GHC.Generics (Generic)

data HiFun = HiFunDiv
           | HiFunMul
           | HiFunAdd
           | HiFunSub
           | HiFunNot
           | HiFunAnd
           | HiFunOr
           | HiFunLessThan
           | HiFunGreaterThan
           | HiFunEquals
           | HiFunNotLessThan
           | HiFunNotGreaterThan
           | HiFunNotEquals
           | HiFunIf
           | HiFunLength
           | HiFunToUpper
           | HiFunToLower
           | HiFunReverse
           | HiFunTrim
           | HiFunList
           | HiFunRange
           | HiFunFold
           | HiFunPackBytes
           | HiFunUnpackBytes
           | HiFunEncodeUtf8
           | HiFunDecodeUtf8
           | HiFunZip
           | HiFunUnzip
           | HiFunSerialise
           | HiFunDeserialise
           | HiFunRead
           | HiFunWrite
           | HiFunMkDir
           | HiFunChDir
           | HiFunParseTime
           | HiFunRand
           | HiFunEcho
           | HiFunCount
           | HiFunKeys
           | HiFunValues
           | HiFunInvert
           deriving (Show, Eq, Ord, Generic)

data HiValue = HiValueBool Bool
             | HiValueFunction HiFun
             | HiValueNumber Rational
             | HiValueNull
             | HiValueString Text
             | HiValueList (Seq HiValue)
             | HiValueBytes ByteString
             | HiValueAction HiAction
             | HiValueTime UTCTime
             | HiValueDict (Map HiValue HiValue)
             deriving (Show, Generic, Eq, Ord)

data HiExpr = HiExprValue HiValue
            | HiExprApply HiExpr [HiExpr]
            | HiExprRun HiExpr
            | HiExprDict [(HiExpr, HiExpr)]
            deriving (Show, Eq)

data HiError = HiErrorInvalidArgument
             | HiErrorInvalidFunction
             | HiErrorArityMismatch
             | HiErrorDivideByZero
             deriving (Show, Eq)

data HiAction = HiActionRead FilePath
              | HiActionWrite FilePath ByteString
              | HiActionMkDir FilePath
              | HiActionChDir FilePath
              | HiActionCwd
              | HiActionNow
              | HiActionRand Int Int
              | HiActionEcho Text
              deriving (Show, Generic, Eq, Ord)

instance Serialise HiAction
instance Serialise HiFun
instance Serialise HiValue

class Monad m => HiMonad m where
  runAction :: HiAction -> m HiValue
