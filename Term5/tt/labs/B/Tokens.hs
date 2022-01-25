{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-missing-signatures #-}
{-# LANGUAGE CPP #-}
{-# LINE 1 "Tokens.x" #-}

module Tokens where

#if __GLASGOW_HASKELL__ >= 603
#include "ghcconfig.h"
#elif defined(__GLASGOW_HASKELL__)
#include "config.h"
#endif
#if __GLASGOW_HASKELL__ >= 503
import Data.Array
#else
import Array
#endif
{-# LINE 1 "templates/wrappers.hs" #-}
-- -----------------------------------------------------------------------------
-- Alex wrapper code.
--
-- This code is in the PUBLIC DOMAIN; you may copy it freely and use
-- it for any purpose whatsoever.





import Data.Word (Word8)
















import Data.Char (ord)
import qualified Data.Bits

-- | Encode a Haskell String to a list of Word8 values, in UTF8 format.
utf8Encode :: Char -> [Word8]
utf8Encode = uncurry (:) . utf8Encode'

utf8Encode' :: Char -> (Word8, [Word8])
utf8Encode' c = case go (ord c) of
                  (x, xs) -> (fromIntegral x, map fromIntegral xs)
 where
  go oc
   | oc <= 0x7f       = ( oc
                        , [
                        ])

   | oc <= 0x7ff      = ( 0xc0 + (oc `Data.Bits.shiftR` 6)
                        , [0x80 + oc Data.Bits..&. 0x3f
                        ])

   | oc <= 0xffff     = ( 0xe0 + (oc `Data.Bits.shiftR` 12)
                        , [0x80 + ((oc `Data.Bits.shiftR` 6) Data.Bits..&. 0x3f)
                        , 0x80 + oc Data.Bits..&. 0x3f
                        ])
   | otherwise        = ( 0xf0 + (oc `Data.Bits.shiftR` 18)
                        , [0x80 + ((oc `Data.Bits.shiftR` 12) Data.Bits..&. 0x3f)
                        , 0x80 + ((oc `Data.Bits.shiftR` 6) Data.Bits..&. 0x3f)
                        , 0x80 + oc Data.Bits..&. 0x3f
                        ])



type Byte = Word8

-- -----------------------------------------------------------------------------
-- The input type
















































































-- -----------------------------------------------------------------------------
-- Token positions

-- `Posn' records the location of a token in the input text.  It has three
-- fields: the address (number of chacaters preceding the token), line number
-- and column of a token within the file. `start_pos' gives the position of the
-- start of the file and `eof_pos' a standard encoding for the end of file.
-- `move_pos' calculates the new position after traversing a given character,
-- assuming the usual eight character tab stops.














-- -----------------------------------------------------------------------------
-- Monad (default and with ByteString input)

























































































































































-- -----------------------------------------------------------------------------
-- Basic wrapper


type AlexInput = (Char,[Byte],String)

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (c,_,_) = c

-- alexScanTokens :: String -> [token]
alexScanTokens str = go ('\n',[],str)
  where go inp__@(_,_bs,s) =
          case alexScan inp__ 0 of
                AlexEOF -> []
                AlexError _ -> error "lexical error"
                AlexSkip  inp__' _ln     -> go inp__'
                AlexToken inp__' len act -> act (take len s) : go inp__'

alexGetByte :: AlexInput -> Maybe (Byte,AlexInput)
alexGetByte (c,(b:bs),s) = Just (b,(c,bs,s))
alexGetByte (_,[],[])    = Nothing
alexGetByte (_,[],(c:s)) = case utf8Encode' c of
                             (b, bs) -> Just (b, (c, bs, s))



-- -----------------------------------------------------------------------------
-- Basic wrapper, ByteString version
































-- -----------------------------------------------------------------------------
-- Posn wrapper

-- Adds text positions to the basic model.













-- -----------------------------------------------------------------------------
-- Posn wrapper, ByteString version














-- -----------------------------------------------------------------------------
-- GScan wrapper

-- For compatibility with previous versions of Alex, and because we can.














alex_tab_size :: Int
alex_tab_size = 8
alex_base :: Array Int Int
alex_base = listArray (0 :: Int, 37)
  [ -8
  , -39
  , -86
  , -41
  , -21
  , -85
  , -102
  , -97
  , -90
  , -13
  , -12
  , -11
  , -40
  , -9
  , 16
  , 0
  , 20
  , 104
  , 130
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 214
  , 240
  , 324
  , 350
  , 434
  , 460
  , 544
  , 570
  , 654
  , 0
  , 0
  ]

alex_table :: Array Int Int
alex_table = listArray (0 :: Int, 909)
  [ 0
  , 14
  , 14
  , 14
  , 14
  , 14
  , 22
  , 26
  , 2
  , 2
  , 2
  , 2
  , 2
  , 2
  , 3
  , 8
  , 9
  , 6
  , 5
  , 4
  , 11
  , 13
  , 21
  , 15
  , 14
  , 14
  , 14
  , 14
  , 14
  , 14
  , 0
  , 0
  , 36
  , 37
  , 10
  , 0
  , 23
  , 12
  , 19
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 14
  , 0
  , 20
  , 0
  , 0
  , 24
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 7
  , 25
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 30
  , 29
  , 30
  , 30
  , 33
  , 30
  , 30
  , 27
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 1
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 34
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 32
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 31
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 28
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 35
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 18
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 17
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 16
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 30
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  , 0
  ]

alex_check :: Array Int Int
alex_check = listArray (0 :: Int, 909)
  [ -1
  , 9
  , 10
  , 11
  , 12
  , 13
  , 45
  , 93
  , 49
  , 50
  , 51
  , 52
  , 53
  , 54
  , 35
  , 117
  , 101
  , 114
  , 108
  , 32
  , 32
  , 32
  , 62
  , 32
  , 32
  , 9
  , 10
  , 11
  , 12
  , 13
  , -1
  , -1
  , 40
  , 41
  , 42
  , -1
  , 44
  , 45
  , 46
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 32
  , -1
  , 58
  , -1
  , -1
  , 61
  , -1
  , -1
  , -1
  , -1
  , -1
  , 39
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 48
  , 49
  , 50
  , 51
  , 52
  , 53
  , 54
  , 55
  , 56
  , 57
  , -1
  , -1
  , -1
  , -1
  , -1
  , 91
  , 92
  , -1
  , -1
  , -1
  , -1
  , 97
  , 98
  , 99
  , 100
  , 101
  , 102
  , 103
  , 104
  , 105
  , 106
  , 107
  , 108
  , 109
  , 110
  , 111
  , 112
  , 113
  , 114
  , 115
  , 116
  , 117
  , 118
  , 119
  , 120
  , 121
  , 122
  , -1
  , 124
  , 97
  , 98
  , 99
  , 100
  , 101
  , 102
  , 103
  , 104
  , 105
  , 106
  , 107
  , 108
  , 109
  , 110
  , 111
  , 112
  , 113
  , 114
  , 115
  , 116
  , 117
  , 118
  , 119
  , 120
  , 121
  , 122
  , 39
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 48
  , 49
  , 50
  , 51
  , 52
  , 53
  , 54
  , 55
  , 56
  , 57
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 39
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 48
  , 49
  , 50
  , 51
  , 52
  , 53
  , 54
  , 55
  , 56
  , 57
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 97
  , 98
  , 99
  , 100
  , 101
  , 102
  , 103
  , 104
  , 105
  , 106
  , 107
  , 108
  , 109
  , 110
  , 111
  , 112
  , 113
  , 114
  , 115
  , 116
  , 117
  , 118
  , 119
  , 120
  , 121
  , 122
  , 97
  , 98
  , 99
  , 100
  , 101
  , 102
  , 103
  , 104
  , 105
  , 106
  , 107
  , 108
  , 109
  , 110
  , 111
  , 112
  , 113
  , 114
  , 115
  , 116
  , 117
  , 118
  , 119
  , 120
  , 121
  , 122
  , 39
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 48
  , 49
  , 50
  , 51
  , 52
  , 53
  , 54
  , 55
  , 56
  , 57
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 39
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 48
  , 49
  , 50
  , 51
  , 52
  , 53
  , 54
  , 55
  , 56
  , 57
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 97
  , 98
  , 99
  , 100
  , 101
  , 102
  , 103
  , 104
  , 105
  , 106
  , 107
  , 108
  , 109
  , 110
  , 111
  , 112
  , 113
  , 114
  , 115
  , 116
  , 117
  , 118
  , 119
  , 120
  , 121
  , 122
  , 97
  , 98
  , 99
  , 100
  , 101
  , 102
  , 103
  , 104
  , 105
  , 106
  , 107
  , 108
  , 109
  , 110
  , 111
  , 112
  , 113
  , 114
  , 115
  , 116
  , 117
  , 118
  , 119
  , 120
  , 121
  , 122
  , 39
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 48
  , 49
  , 50
  , 51
  , 52
  , 53
  , 54
  , 55
  , 56
  , 57
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 39
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 48
  , 49
  , 50
  , 51
  , 52
  , 53
  , 54
  , 55
  , 56
  , 57
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 97
  , 98
  , 99
  , 100
  , 101
  , 102
  , 103
  , 104
  , 105
  , 106
  , 107
  , 108
  , 109
  , 110
  , 111
  , 112
  , 113
  , 114
  , 115
  , 116
  , 117
  , 118
  , 119
  , 120
  , 121
  , 122
  , 97
  , 98
  , 99
  , 100
  , 101
  , 102
  , 103
  , 104
  , 105
  , 106
  , 107
  , 108
  , 109
  , 110
  , 111
  , 112
  , 113
  , 114
  , 115
  , 116
  , 117
  , 118
  , 119
  , 120
  , 121
  , 122
  , 39
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 48
  , 49
  , 50
  , 51
  , 52
  , 53
  , 54
  , 55
  , 56
  , 57
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 39
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 48
  , 49
  , 50
  , 51
  , 52
  , 53
  , 54
  , 55
  , 56
  , 57
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 97
  , 98
  , 99
  , 100
  , 101
  , 102
  , 103
  , 104
  , 105
  , 106
  , 107
  , 108
  , 109
  , 110
  , 111
  , 112
  , 113
  , 114
  , 115
  , 116
  , 117
  , 118
  , 119
  , 120
  , 121
  , 122
  , 97
  , 98
  , 99
  , 100
  , 101
  , 102
  , 103
  , 104
  , 105
  , 106
  , 107
  , 108
  , 109
  , 110
  , 111
  , 112
  , 113
  , 114
  , 115
  , 116
  , 117
  , 118
  , 119
  , 120
  , 121
  , 122
  , 39
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 48
  , 49
  , 50
  , 51
  , 52
  , 53
  , 54
  , 55
  , 56
  , 57
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 39
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 48
  , 49
  , 50
  , 51
  , 52
  , 53
  , 54
  , 55
  , 56
  , 57
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 97
  , 98
  , 99
  , 100
  , 101
  , 102
  , 103
  , 104
  , 105
  , 106
  , 107
  , 108
  , 109
  , 110
  , 111
  , 112
  , 113
  , 114
  , 115
  , 116
  , 117
  , 118
  , 119
  , 120
  , 121
  , 122
  , 97
  , 98
  , 99
  , 100
  , 101
  , 102
  , 103
  , 104
  , 105
  , 106
  , 107
  , 108
  , 109
  , 110
  , 111
  , 112
  , 113
  , 114
  , 115
  , 116
  , 117
  , 118
  , 119
  , 120
  , 121
  , 122
  , 39
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 48
  , 49
  , 50
  , 51
  , 52
  , 53
  , 54
  , 55
  , 56
  , 57
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , 97
  , 98
  , 99
  , 100
  , 101
  , 102
  , 103
  , 104
  , 105
  , 106
  , 107
  , 108
  , 109
  , 110
  , 111
  , 112
  , 113
  , 114
  , 115
  , 116
  , 117
  , 118
  , 119
  , 120
  , 121
  , 122
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  ]

alex_deflt :: Array Int Int
alex_deflt = listArray (0 :: Int, 37)
  [ -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  , -1
  ]

alex_accept = listArray (0 :: Int, 37)
  [ AlexAccNone
  , AlexAccNone
  , AlexAccNone
  , AlexAccNone
  , AlexAccNone
  , AlexAccNone
  , AlexAccNone
  , AlexAccNone
  , AlexAccNone
  , AlexAccNone
  , AlexAccNone
  , AlexAccNone
  , AlexAccNone
  , AlexAccNone
  , AlexAccSkip
  , AlexAcc 22
  , AlexAcc 21
  , AlexAcc 20
  , AlexAcc 19
  , AlexAcc 18
  , AlexAcc 17
  , AlexAcc 16
  , AlexAcc 15
  , AlexAcc 14
  , AlexAcc 13
  , AlexAcc 12
  , AlexAcc 11
  , AlexAcc 10
  , AlexAcc 9
  , AlexAcc 8
  , AlexAcc 7
  , AlexAcc 6
  , AlexAcc 5
  , AlexAcc 4
  , AlexAcc 3
  , AlexAcc 2
  , AlexAcc 1
  , AlexAcc 0
  ]

alex_actions = array (0 :: Int, 23)
  [ (22,alex_action_1)
  , (21,alex_action_2)
  , (20,alex_action_3)
  , (19,alex_action_4)
  , (18,alex_action_5)
  , (17,alex_action_6)
  , (16,alex_action_7)
  , (15,alex_action_8)
  , (14,alex_action_9)
  , (13,alex_action_10)
  , (12,alex_action_11)
  , (11,alex_action_12)
  , (10,alex_action_13)
  , (9,alex_action_13)
  , (8,alex_action_13)
  , (7,alex_action_13)
  , (6,alex_action_13)
  , (5,alex_action_13)
  , (4,alex_action_13)
  , (3,alex_action_13)
  , (2,alex_action_13)
  , (1,alex_action_14)
  , (0,alex_action_15)
  ]

{-# LINE 26 "Tokens.x" #-}


-- The token type:
data Token = TokenIndent
           | TokenForall
           | TokenLet
           | TokenIn
           | TokenDot
           | TokenColon
           | TokenArrow
           | TokenVdash
           | TokenComma
           | TokenAssign
           | TokenLambda
           | TokenRule Int
           | TokenVar String
	   | TokenLParen
	   | TokenRParen
            deriving (Eq,Show)

scanTokens = alexScanTokens


alex_action_1 =  \s -> TokenIndent 
alex_action_2 =  \s -> TokenForall 
alex_action_3 =  \s -> TokenLet 
alex_action_4 =  \s -> TokenIn 
alex_action_5 =  \s -> TokenDot 
alex_action_6 =  \s -> TokenColon 
alex_action_7 =  \s -> TokenArrow 
alex_action_8 =  \s -> TokenVdash 
alex_action_9 =  \s -> TokenComma 
alex_action_10 =  \s -> TokenAssign 
alex_action_11 =  \s -> TokenLambda 
alex_action_12 =  \s -> TokenRule $ read $ take 1 $ drop 7 $ s 
alex_action_13 =  \s -> TokenVar s 
alex_action_14 =  \s -> TokenLParen 
alex_action_15 =  \s -> TokenRParen 
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- -----------------------------------------------------------------------------
-- ALEX TEMPLATE
--
-- This code is in the PUBLIC DOMAIN; you may copy it freely and use
-- it for any purpose whatsoever.

-- -----------------------------------------------------------------------------
-- INTERNALS and main scanner engine




































































alexIndexInt16OffAddr arr off = arr ! off
























alexIndexInt32OffAddr arr off = arr ! off











quickIndex arr i = arr ! i


-- -----------------------------------------------------------------------------
-- Main lexing routines

data AlexReturn a
  = AlexEOF
  | AlexError  !AlexInput
  | AlexSkip   !AlexInput !Int
  | AlexToken  !AlexInput !Int a

-- alexScan :: AlexInput -> StartCode -> AlexReturn a
alexScan input__ (sc)
  = alexScanUser undefined input__ (sc)

alexScanUser user__ input__ (sc)
  = case alex_scan_tkn user__ input__ (0) input__ sc AlexNone of
  (AlexNone, input__') ->
    case alexGetByte input__ of
      Nothing ->



                                   AlexEOF
      Just _ ->



                                   AlexError input__'

  (AlexLastSkip input__'' len, _) ->



    AlexSkip input__'' len

  (AlexLastAcc k input__''' len, _) ->



    AlexToken input__''' len (alex_actions ! k)


-- Push the input through the DFA, remembering the most recent accepting
-- state it encountered.

alex_scan_tkn user__ orig_input len input__ s last_acc =
  input__ `seq` -- strict in the input
  let
  new_acc = (check_accs (alex_accept `quickIndex` (s)))
  in
  new_acc `seq`
  case alexGetByte input__ of
     Nothing -> (new_acc, input__)
     Just (c, new_input) ->



      case fromIntegral c of { (ord_c) ->
        let
                base   = alexIndexInt32OffAddr alex_base s
                offset = (base + ord_c)
                check  = alexIndexInt16OffAddr alex_check offset

                new_s = if (offset >= (0)) && (check == ord_c)
                          then alexIndexInt16OffAddr alex_table offset
                          else alexIndexInt16OffAddr alex_deflt s
        in
        case new_s of
            (-1) -> (new_acc, input__)
                -- on an error, we want to keep the input *before* the
                -- character that failed, not after.
            _ -> alex_scan_tkn user__ orig_input (if c < 0x80 || c >= 0xC0 then (len + (1)) else len)
                                                -- note that the length is increased ONLY if this is the 1st byte in a char encoding)
                        new_input new_s new_acc
      }
  where
        check_accs (AlexAccNone) = last_acc
        check_accs (AlexAcc a  ) = AlexLastAcc a input__ (len)
        check_accs (AlexAccSkip) = AlexLastSkip  input__ (len)

        check_accs (AlexAccPred a predx rest)
           | predx user__ orig_input (len) input__
           = AlexLastAcc a input__ (len)
           | otherwise
           = check_accs rest
        check_accs (AlexAccSkipPred predx rest)
           | predx user__ orig_input (len) input__
           = AlexLastSkip input__ (len)
           | otherwise
           = check_accs rest


data AlexLastAcc
  = AlexNone
  | AlexLastAcc !Int !AlexInput !Int
  | AlexLastSkip     !AlexInput !Int

data AlexAcc user
  = AlexAccNone
  | AlexAcc Int
  | AlexAccSkip

  | AlexAccPred Int (AlexAccPred user) (AlexAcc user)
  | AlexAccSkipPred (AlexAccPred user) (AlexAcc user)

type AlexAccPred user = user -> AlexInput -> Int -> AlexInput -> Bool

-- -----------------------------------------------------------------------------
-- Predicates on a rule

alexAndPred p1 p2 user__ in1 len in2
  = p1 user__ in1 len in2 && p2 user__ in1 len in2

--alexPrevCharIsPred :: Char -> AlexAccPred _
alexPrevCharIs c _ input__ _ _ = c == alexInputPrevChar input__

alexPrevCharMatches f _ input__ _ _ = f (alexInputPrevChar input__)

--alexPrevCharIsOneOfPred :: Array Char Bool -> AlexAccPred _
alexPrevCharIsOneOf arr _ input__ _ _ = arr ! alexInputPrevChar input__

--alexRightContext :: Int -> AlexAccPred _
alexRightContext (sc) user__ _ _ input__ =
     case alex_scan_tkn user__ input__ (0) input__ sc AlexNone of
          (AlexNone, _) -> False
          _ -> True
        -- TODO: there's no need to find the longest
        -- match when checking the right context, just
        -- the first match will do.

