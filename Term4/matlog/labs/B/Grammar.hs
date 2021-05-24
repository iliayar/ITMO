module Grammar (parseProof) where
import qualified Parser as P
import           Parser ((<|>))
import           Proof

parseFile :: P.Parser File
parseFile = do
    context <- parseContext <* P.spaces
    P.exact "|-" <* P.spaces
    expr <- parseExpression <* P.spaces
    P.char '\n' <* P.spaces
    lines <- P.many (parseLine <* P.spaces)
    return $ File context expr lines

parseContext :: P.Parser Context
parseContext = P.choice "context" 
    [ do
        exprs <- P.spaces *> P.sepBy1 (parseExpression <* P.spaces) (P.char ',' >> P.spaces)
        return $ Context exprs
    , return EmptyContext ]

parseLine :: P.Parser Expression
parseLine = do
    expr <- parseExpression
    P.char '\n'
    return $ expr

parseExpression0 :: P.Parser Expression
parseExpression0 = P.choice "negate, parenthesis or variable"
    [ do
        P.char '!' <* P.spaces
        expr <- parseExpression0 <* P.spaces
        return $ Not expr
    , do
        expr <- P.char '(' *> P.spaces *> parseExpression <* P.spaces <* P.char ')'
        return expr
    , do
        var <- parseVar
        return $ var ]


parseExpression1 :: P.Parser Expression
parseExpression1 = P.choice "and binary operator"
    [ do
        exprs <- P.sepBy1 (parseExpression0 <* P.spaces) (P.exact "&" >> P.spaces)
        return $ foldl1 And exprs
    , parseExpression0 ]

parseExpression2 :: P.Parser Expression
parseExpression2 = P.choice "or binary operator"
    [ do
        exprs <- P.sepBy1 (parseExpression1 <* P.spaces) (P.exact "|" >> P.spaces)
        return $ foldl1 Or exprs
    , parseExpression1 ]

parseExpression3 :: P.Parser Expression
parseExpression3 = P.choice "impl binary operator"
    [ do
        exprs <- P.sepBy1 (parseExpression2 <* P.spaces) (P.exact "->" >> P.spaces)
        return $ foldr1 Impl exprs
    , parseExpression2 ]

parseExpression :: P.Parser Expression
parseExpression = parseExpression3

parseVar :: P.Parser Expression
parseVar = do
    first <- P.alpha
    rest <- P.many (P.alphaNum <|> P.char '\'')
    return $ Var (first:rest) 

parser = parseFile
parseProof = P.runParser parser
