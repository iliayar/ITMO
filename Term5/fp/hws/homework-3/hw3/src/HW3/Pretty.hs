{-# OPTIONS_GHC -fno-warn-orphans #-}

module HW3.Pretty
  ( prettyValue ) where

import Data.Bool (bool)
import qualified Data.ByteString as BS
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.Ratio (denominator, numerator, (%))
import Data.Scientific (FPFormat (Fixed), formatScientific, fromRationalRepetendUnlimited)
import Data.Word (Word8)
import HW3.Base
import HW3.Helpers
import Prettyprinter
import Prettyprinter.Render.Terminal (AnsiStyle)
import Text.Printf (printf)

instance Pretty HiAction where
  pretty (HiActionWrite file content) = pretty "write" <> parens
    (dquotes (pretty file) <> pretty ", " <> prettyByteString content)
  pretty (HiActionRead file) = prettyFun "read" file
  pretty (HiActionMkDir path) = prettyFun "mkdir" path
  pretty (HiActionChDir path) = prettyFun "cd" path
  pretty HiActionCwd  = pretty "cwd"
  pretty HiActionNow  = pretty "now"
  pretty (HiActionRand from to) = pretty "rand" <> parens (pretty from <> pretty ", " <> pretty to)
  pretty (HiActionEcho s) = prettyFun "echo" s


-- | Helper, convert fun name and single string argument into human
-- readable representation
prettyFun :: Pretty a => String -> a -> Doc ann
prettyFun f arg = pretty f <> parens (dquotes (pretty arg))

instance Pretty HiValue where
  pretty (HiValueNumber n)     = prettyNumber n
  pretty (HiValueFunction fun) = pretty fun
  pretty (HiValueBool True)    = pretty "true"
  pretty (HiValueBool False)   = pretty "false"
  pretty HiValueNull           = pretty "null"
  pretty (HiValueString s)     = viaShow s
  pretty (HiValueList l)       = brackets $ concatWith (surround (pretty ",")) (fmap ((space <>) . pretty) l) <> space
  pretty (HiValueBytes bs)     = prettyByteString bs
  pretty (HiValueAction act)   = pretty act
  pretty (HiValueTime t)       = prettyFun "parse-time" (show t)
  pretty (HiValueDict d)       = braces $
    concatWith (surround (pretty ",")) (map prettyKeyValue $ M.toList d) <> space
    where
      prettyKeyValue :: (Pretty k, Pretty v) => (k, v) -> Doc ann
      prettyKeyValue (k, v) = space <> pretty k <> pretty ":" <+> pretty v

instance Pretty HiFun where
  pretty f = pretty $ fromJust $ lookup f hiFunsStrings

-- | Convert byte list into human readable format.
-- + Integer numbers: 1, 54
-- + Finite decimal numbers: 1.004, 13.37
-- + Infinite decimal numbers: 1 + 42/54
prettyNumber :: Rational -> Doc ann
prettyNumber n =
  let denom = denominator n
  in case quotRem (numerator n) denom of
       (int, 0) -> viaShow int
       (int, r) ->
         case fromRationalRepetendUnlimited n of
           (sci, Nothing) -> pretty $ formatScientific Fixed Nothing sci
           (_, Just _) ->
             let frac = pretty (abs r) <> pretty "/" <> pretty (abs denom)
                 neg = r % denom < 0 % 1
             in if int == 0
                   then pretty (bool "" "-" neg) <> frac
                   else pretty int <+> pretty (bool "+" "-" neg) <+> frac

-- | Convert byte list into human readable format
prettyByteString :: BS.ByteString -> Doc ann
prettyByteString bs = pretty "[#" <> concatWith (<>) (map ((space <>) . pretty . showHex) $ BS.unpack bs) <+> pretty "#]"
    where
      showHex :: Word8 -> String
      showHex = printf "%02x"

-- | Convert `HiValue` into human readable string
prettyValue :: HiValue -> Doc AnsiStyle
prettyValue = pretty
