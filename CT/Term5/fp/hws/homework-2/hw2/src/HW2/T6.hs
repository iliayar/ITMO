{-# LANGUAGE BlockArguments             #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module HW2.T6
  ( parseExpr
  , ParseError (..) ) where

import Control.Applicative (Alternative, empty, many, optional, some, (<|>))
import Control.Monad (MonadPlus, mfilter)
import qualified Data.Char
import Data.Foldable (msum)
import Data.Functor (void)
import Data.List (foldl')
import Data.Scientific (scientific, toRealFloat)
import HW2.T1 (Annotated (..), Except (..))
import HW2.T4 (Expr (..), Prim (..))
import HW2.T5 (ExceptState (..))
import Numeric.Natural (Natural)

-- |Data type represents and parsing error
data ParseError
  = ErrorAtPos Natural -- ^ Provide a position when parsing failed

newtype Parser a = P (ExceptState ParseError (Natural, String) a)
  deriving newtype (Functor, Applicative, Monad)

runP :: Parser a -> String -> Except ParseError a
runP (P p) s =
  case runES p (0, s) of
    Error e          -> Error e
    Success (a :# _) -> Success a

-- When string is empty we abort computatiotn with an error with
-- current position. When string is not empty we replace state with
-- position incremented and the rest of the string and change value to
-- consumed character.
pChar :: Parser Char
pChar = P $ ES \(pos, s) ->
  case s of
    []     -> Error (ErrorAtPos pos)
    (c:cs) -> Success (c :# (pos + 1, cs))

parseError :: Parser a
parseError = P $ ES \(pos, _) -> Error (ErrorAtPos pos)

instance Alternative Parser where
  empty = parseError
  (P p1) <|> (P p2) = P $ ES \(pos, s) ->
    case runES p1 (pos, s) of
      Error _ ->
        case runES p2 (pos, s) of
          Error _ -> Error (ErrorAtPos pos)
          ok      -> ok
      ok -> ok

instance MonadPlus Parser

pEof :: Parser ()
pEof = P $ ES \(pos, s) ->
  case s of
    [] -> Success (() :# (pos, s))
    _  -> Error (ErrorAtPos pos)

ws :: Parser ()
ws = void $ many (char Data.Char.isSpace)

char :: (Char -> Bool) -> Parser Char
char = flip mfilter pChar

parseNumber :: Parser Double
parseNumber = do
  int <- some parseDigit
  _ <- char (=='.')
  frac <- many parseDigit
  return $ convertDouble int frac
  where
    parseDigit :: Parser Integer
    parseDigit = toInteger . flip (-) (Data.Char.ord '0') . Data.Char.ord
      <$> char Data.Char.isDigit

    convertInt :: [Integer] -> Integer
    convertInt = foldl' (\acc n -> acc * 10 + n) 0

    convertDouble :: [Integer] -> [Integer] -> Double
    convertDouble int frac = toRealFloat
      $ scientific (convertInt $ int ++ frac) (negate $ length frac)

-- |Parse expression from a string. Result in error when parsing
-- failing
parseExpr :: String -> Except ParseError Expr
parseExpr = runP parseExprWithEnd
  where
    parseExprLeftAssoc :: Parser Expr -> String -> Parser Expr
    parseExprLeftAssoc parseNext ops = do
      first <- ws *> parseNext <* ws
      parseExprLeftAssoc' first
      where
        parseExprLeftAssoc' :: Expr -> Parser Expr
        parseExprLeftAssoc' acc = do
          maybeOp <- optional $ parseOp ops
          case maybeOp of
            Nothing -> return acc
            Just op -> do
              second <- ws *> parseNext <* ws
              parseExprLeftAssoc' (Op $ op acc second)

    parseExpr' :: Parser Expr
    parseExpr' = parseExprLeftAssoc parseFactor "+-"

    parseExprWithEnd :: Parser Expr
    parseExprWithEnd = parseExpr' <* ws <* pEof

    parseFactor :: Parser Expr
    parseFactor = parseExprLeftAssoc parseTerm "*/"

    parseTerm :: Parser Expr
    parseTerm = ws *> msum
                [ Val <$> parseNumber
                , char (=='(') *> ws *> parseExpr' <* ws <* char (==')') ]

    parseOp :: String -> Parser (Expr -> Expr -> Prim Expr)
    parseOp ops = do
      op <- ws *> char (`elem` ops)
      return
        case op of
          '+' -> Add
          '-' -> Sub
          '*' -> Mul
          '/' -> Div
          _   -> error "unreachable"
