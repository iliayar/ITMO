{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE OverloadedStrings #-}

module HW3.Parser
  ( parse ) where

import Control.Monad (replicateM)
import Control.Monad.Combinators.Expr
import Data.Bool (bool)
import qualified Data.ByteString as BS
import Data.Char (isAlpha, isAlphaNum)
import Data.List (intercalate)
import Data.Maybe (isJust)
import Data.Ratio ((%))
import Data.Scientific (Scientific (base10Exponent, coefficient))
import qualified Data.Text as T
import Data.Void (Void)
import HW3.Base
import HW3.Helpers
import Numeric (readHex)
import Text.Megaparsec hiding (parse)
import qualified Text.Megaparsec as MP
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

-- | Parsec parser type alias
type Parser = Parsec Void String

-- | Parses expression into internal `HiExpr` representation
parse :: String -> Either (ParseErrorBundle String Void) HiExpr
parse = MP.parse (wsWrap pHiInfixExpr <* eof) ""

-- | Main parser. Parses function aplications, postifx operators (`!`, `.fld`) and infix binary operators
pHiInfixExpr :: Parser HiExpr
pHiInfixExpr = makeExprParser (wsWrap $ pHiExprParen <|> pHiExprValue)
  [ [ Postfix $ manyPostfix $ choice
      [ dotOp
      , pHiExprRun
      , pHiFunArgsPostfix ] ]
  , [ binary' InfixL  (without "/" "=") HiFunDiv
    , binaryL "*" HiFunMul ]
  , [ binaryL "+" HiFunAdd
    , binaryL "-" HiFunSub ]
  , [ binary' InfixN (without "<" "=") HiFunLessThan
    , binary' InfixN (without ">" "=") HiFunGreaterThan
    , binaryN ">=" HiFunNotLessThan
    , binaryN "<=" HiFunNotGreaterThan
    , binaryN "==" HiFunEquals
    , binaryN "/=" HiFunNotEquals ]
  , [ binaryR "&&" HiFunAnd ]
  , [ binaryR "||" HiFunOr ] ]
  where
    without s n = try (string s <* notFollowedBy n)

    binaryL :: String -> HiFun -> Operator Parser HiExpr
    binaryL = binary InfixL

    binaryR :: String -> HiFun -> Operator Parser HiExpr
    binaryR = binary InfixR

    binaryN :: String -> HiFun -> Operator Parser HiExpr
    binaryN = binary InfixN

    binary' :: (Parser (HiExpr -> HiExpr -> HiExpr) -> Operator Parser HiExpr)
           -> Parser a
           -> HiFun
           -> Operator Parser HiExpr
    binary' ctr pOp fun =
      ctr ((\a b ->
              HiExprApply (HiExprValue $ HiValueFunction fun) [a, b]
           ) <$ wsWrap pOp)

    binary :: (Parser (HiExpr -> HiExpr -> HiExpr) -> Operator Parser HiExpr)
           -> String
           -> HiFun
           -> Operator Parser HiExpr
    binary ctr op fun = binary' ctr (string op) fun

    manyPostfix :: Parser (a -> a) -> Parser (a -> a)
    manyPostfix p = foldl1 (flip (.)) <$> some p

    dotOpFld :: Parser T.Text
    dotOpFld = wsWrap $ do
      _ <- char '.'
      fld <- ((:) <$> satisfy isAlpha <*> many (satisfy isAlphaNum)) `sepBy1` char '-'
      pure $ T.pack $ intercalate "-" fld

    dotOp :: Parser (HiExpr -> HiExpr)
    dotOp = (\ fld obj -> HiExprApply obj [HiExprValue $ HiValueString fld]) <$> dotOpFld

    pHiExprParen :: Parser HiExpr
    pHiExprParen = wsWrap $ char '(' *> pHiInfixExpr <* char ')'

    pHiFunArgs :: Parser [HiExpr]
    pHiFunArgs = wsWrap $ do
      _ <- char '('
      args <- pHiExprCommaSeparated
      _ <- char ')'
      pure args

    pHiFunArgsPostfix :: Parser (HiExpr -> HiExpr)
    pHiFunArgsPostfix = flip HiExprApply <$> pHiFunArgs

    pHiExprRun :: Parser (HiExpr -> HiExpr)
    pHiExprRun = HiExprRun <$ wsWrap (string "!")

-- | Parses the any `HiValue` and makes it `HiExpr`
pHiExprValue :: Parser HiExpr
pHiExprValue = HiExprValue <$> pHiValue <|> pHiValueList <|> pHiExprDict

-- | Parses dictionary
pHiExprDict :: Parser HiExpr
pHiExprDict = do
  _ <- wsWrap $ char '{'
  elems <- sepBy pDictElem (wsWrap $ char ',')
  _ <- wsWrap $ char '}'
  pure $ HiExprDict elems
  where
    pDictElem :: Parser (HiExpr, HiExpr)
    pDictElem = do
      key <- pHiInfixExpr
      _ <- wsWrap $ char ':'
      value <- pHiInfixExpr
      pure (key, value)

-- | Parses numbers, actions, builtin function names, byte arrays,
-- booleans, string literals and `null`
pHiValue :: Parser HiValue
pHiValue = wsWrap $ choice
  [ pHiValueNumber
  , pHiValueAction
  , pHiValueFuntion
  , pHiValueBytes
  , pHiValueBool
  , pHiValueString
  , HiValueNull <$ string "null" ]

-- | Parses number, wraps it into `HuValue`
pHiValueNumber :: Parser HiValue
pHiValueNumber = HiValueNumber <$> pRational

-- | Parses builtin function name, wraps it into `HuValue`
pHiValueFuntion :: Parser HiValue
pHiValueFuntion = HiValueFunction <$> pHiFun

-- | Parses boolean, wraps it into `HuValue`
pHiValueBool :: Parser HiValue
pHiValueBool = HiValueBool <$> choice
  [ True  <$ string "true"
  , False <$ string "false" ]

-- | Parses string literal, wraps it into `HuValue`
pHiValueString :: Parser HiValue
pHiValueString =
  HiValueString . T.pack <$> (char '"' >> manyTill L.charLiteral (char '"'))

-- | Parses number literal into `Rational`
pRational :: Parser Rational
pRational = do
  neg <- isJust <$> optional (char '-') <* ws
  res <- sciToRat <$> L.scientific
  pure $ bool res (negate res) neg
  where
    sciToRat :: Scientific -> Rational
    sciToRat n =
      let expo = toInteger $ base10Exponent n
          mantis = coefficient n
      in if expo < 0
      then mantis % (10 ^ negate expo)
      else mantis * (10 ^ expo) % 1

-- | Parses list into `HiFunList` function application
pHiValueList :: Parser HiExpr
pHiValueList = do
  _ <- ws >> char '['
  args <- pHiExprCommaSeparated
  _ <- char ']' >> ws
  pure $ HiExprApply (HiExprValue $ HiValueFunction HiFunList) args

-- | Parses byte list, wrap it into `HiValue`
pHiValueBytes :: Parser HiValue
pHiValueBytes = do
  _ <- string "[#"
  bs <- wsWrap $ flip sepBy spaceSep $ do
    num <- replicateM 2 hexDigitChar
    pure $ fst $ head $ readHex num
  _ <- string "#]"
  pure $ HiValueBytes $ BS.pack bs
  where
    spaceSep = try $ space1 >> ws <* notFollowedBy "#"

-- | Parses action string, wrap it into `HiValue`
pHiValueAction :: Parser HiValue
pHiValueAction = HiValueAction <$> choice
  [ HiActionCwd <$ string "cwd"
  , HiActionNow <$ string "now" ]

-- | Prarses builing function name
pHiFun :: Parser HiFun
pHiFun = choice $ map (\(f, s) -> f <$ string s) hiFunsStrings

-- | Helper, parses one line comment
pLineComment :: Parser ()
pLineComment = empty

-- | Helper, parses block comment
pBlockComment :: Parser ()
pBlockComment = L.skipBlockComment "{-" "-}"

-- | Helper, parses whitespace, line or block comments
ws :: Parser ()
ws = L.space space1 pLineComment pBlockComment

-- | Helper, surround parser with possible whitespaces and comments
wsWrap :: Parser a -> Parser a
wsWrap p = ws *> p <* ws

-- | Parses `HiExpr` separated by comma
pHiExprCommaSeparated :: Parser [HiExpr]
pHiExprCommaSeparated = wsWrap $ sepBy (wsWrap pHiInfixExpr) $ char ','
