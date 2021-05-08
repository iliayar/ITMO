module Parser where

import Data.Char (isSpace, isDigit, isAlpha)

data ParseError = ParseError String String
instance Show ParseError where
    show (ParseError expect get) = "Expected: " ++ expect ++ ". Get: " ++ get

newtype Parser a = Parser {
    runParser :: String -> (String, Either ParseError a)
}

instance Functor Parser where
    fmap f p = Parser {
        runParser = 
            \input -> case runParser p input of
                (xs, Left err) -> (xs, Left err)
                (xs, Right value) -> (xs, Right $ f value)
    }
instance Applicative Parser where
    pure = return
    pf <*> p = Parser {
        runParser = \input ->
            case runParser pf input of
                (xs, Left err) -> (xs, Left err)
                (xs, Right f) ->
                    case runParser p xs of
                        (xs, Left err) -> (xs, Left err)
                        (xs, Right value) -> (xs, Right $ f value)
    }
    --liftA2 f2 p1 p2 = Parser {
        --runParser = \input ->
            --case runParser p1 input of
                --(xs, Left err) -> (xs, Left err)
                --(xs, Right v1) ->
                    --case runParser p2 xs of
                        --(xs, Left err) -> (xs, Left err)
                        --(xs, Right v2) -> (xs, Right $ f2 v1 v2)
    --}
instance Monad Parser where
    p >>= f = Parser {
        runParser =
            \input -> case runParser p input of
                (xs, Left err) -> (xs, Left err)
                (xs, Right value) -> runParser (f value) xs
    }

    return value = Parser {
        runParser = \input -> (input, Right value)
    }

parseError :: String -> String -> Parser a
parseError exp get = Parser {
    runParser =
        \input -> (input, Left $ ParseError exp get)
}

any :: Parser Char
any = Parser {
    runParser = 
        \input -> case input of
            (x:xs) -> (xs, Right x)
            [] -> ("", Left $ ParseError 
                "any character"
                "the end of input"
                )
}

eof :: Parser ()
eof = Parser {
    runParser = 
        \input -> case input of
            (x:_) -> (input, Left $ ParseError
                        "the end of input"
                        [x]
                    )        
            [] -> ("", Right ())
}

try:: Parser a -> Parser a
try p = Parser {
    runParser =
        \input -> case runParser p input of
            (xs, Left err) -> (input, Left err)
            success -> success
}

(<|>) :: Parser a -> Parser a -> Parser a
p1 <|> p2 = Parser {
    runParser =
        \input -> 
            case runParser p1 input of
                (input', Left err) -> runParser p2 input
                    -- | input' == input -> runParser p2 input
                    -- | otherwise -> (input', Left err)
                success -> success
}

choice :: String -> [Parser a] -> Parser a
choice descr = foldr (<|>) noMatch
    where noMatch = parseError descr "no match"

satisfy :: String -> (Char -> Bool) -> Parser Char
satisfy descr pred = try $ do
    c <- Parser.any
    if pred c 
        then return c
        else parseError descr [c]
        
many, many1 :: Parser a -> Parser [a]
many p = many1 p <|> return []
many1 p = do
    first <- p
    rest <- many p
    return (first:rest)

sepBy, sepBy1 :: Parser a -> Parser s -> Parser [a]
sepBy p s = sepBy1 p s <|> return []
sepBy1 p s = do
    first <- p
    rest <- many (s >> p)
    return (first:rest)

char :: Char -> Parser Char
char c = satisfy [c] (== c)

whitespace :: Parser Char
whitespace = satisfy "space" (`elem` " \t\r")

digit :: Parser Char
digit = satisfy "digit" isDigit

alpha = satisfy "alpha" isAlpha

alphaNum = choice "alphaNum" [alpha, digit]

spaces, spaces1 :: Parser [Char]
spaces1 = many1 whitespace
spaces = many whitespace

exact :: String -> Parser ()
exact s = foldr (>>) (return ()) $ map char s
