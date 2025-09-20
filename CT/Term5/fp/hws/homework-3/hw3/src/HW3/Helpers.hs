module HW3.Helpers
 ( ratToInteger
 , ratToInt
 , ratToByte
 , hiFunsStrings
 , unreachable
 , strictCompress
 , strictDecompress
 , strictSerialise
 , strictDeserialise ) where

import qualified Codec.Compression.Zlib as Z
import qualified Codec.Serialise as SR
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import Data.Ratio (denominator, numerator)
import HW3.Base
import qualified Prelude.SafeEnum as SE

unreachable :: a
unreachable = error "unreachable"

ratToInteger :: Rational -> Maybe Integer
ratToInteger r =
  case quotRem (numerator r) (denominator r) of
    (n, 0) -> Just n
    _      -> Nothing

ratToInt :: Rational -> Maybe Int
ratToInt r = ratToInteger r >>= SE.fromEnum

ratToByte :: Rational -> Maybe Integer
ratToByte r = (\n -> if n < 0 || n > 255 then Nothing else Just n) =<< ratToInteger r

strictCompress :: BS.ByteString -> BS.ByteString
strictCompress = LBS.toStrict . Z.compressWith (Z.defaultCompressParams { Z.compressLevel = Z.bestCompression }) . LBS.fromStrict

strictDecompress :: BS.ByteString -> BS.ByteString
strictDecompress = LBS.toStrict . Z.decompress . LBS.fromStrict

strictSerialise :: SR.Serialise a => a -> BS.ByteString
strictSerialise = LBS.toStrict . SR.serialise

strictDeserialise :: SR.Serialise a => BS.ByteString -> Maybe a
strictDeserialise = either (const Nothing) Just . SR.deserialiseOrFail  . LBS.fromStrict

hiFunsStrings :: [(HiFun, String)]
hiFunsStrings =
  [ (HiFunDiv            , "div")
  , (HiFunMul            , "mul")
  , (HiFunAdd            , "add")
  , (HiFunSub            , "sub")
  , (HiFunAnd            , "and")
  , (HiFunOr             , "or")
  , (HiFunLessThan       , "less-than")
  , (HiFunGreaterThan    , "greater-than")
  , (HiFunEquals         , "equals")
  , (HiFunNotLessThan    , "not-less-than")
  , (HiFunNotGreaterThan , "not-greater-than")
  , (HiFunNotEquals      , "not-equals")
  , (HiFunNot            , "not")
  , (HiFunIf             , "if")
  , (HiFunLength         , "length")
  , (HiFunToUpper        , "to-upper")
  , (HiFunToLower        , "to-lower")
  , (HiFunReverse        , "reverse")
  , (HiFunTrim           , "trim")
  , (HiFunList           , "list")
  , (HiFunRange          , "range")
  , (HiFunFold           , "fold")
  , (HiFunPackBytes      , "pack-bytes")
  , (HiFunUnpackBytes    , "unpack-bytes")
  , (HiFunZip            , "zip")
  , (HiFunUnzip          , "unzip")
  , (HiFunEncodeUtf8     , "encode-utf8")
  , (HiFunDecodeUtf8     , "decode-utf8")
  , (HiFunSerialise      , "serialise")
  , (HiFunDeserialise    , "deserialise")
  , (HiFunRead           , "read")
  , (HiFunWrite          , "write")
  , (HiFunMkDir          , "mkdir")
  , (HiFunChDir          , "cd")
  , (HiFunParseTime      , "parse-time")
  , (HiFunRand           , "rand")
  , (HiFunEcho           , "echo")
  , (HiFunCount          , "count")
  , (HiFunKeys           , "keys")
  , (HiFunValues         , "values")
  , (HiFunInvert         , "invert") ]
