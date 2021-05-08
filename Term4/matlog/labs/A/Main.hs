import qualified Parser as P


data File =  File Context Expression [Line]
    deriving (Show)
data Context = Context [Expression] 
             | EmptyContext
    deriving (Show)
data Line = Line Expression
    deriving (Show)
data Expression = And Expression Expression
                | Or Expression Expression
                | Impl Expression Expression
                | Not Expression
                | Parenthesis Expression
                | ExprVar Var
    deriving (Show)
data Var = Var String
    deriving (Show)

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

parseLine :: P.Parser Line
parseLine = do
    expr <- parseExpression
    P.char '\n'
    return $ Line expr

parseExpression :: P.Parser Expression
parseExpression = P.choice "expression"
    [ do
        left <- parseExpression <* P.spaces
        ctr <- P.choice "binary operator"
            [ do 
                P.char '&' <* P.spaces
                return And
            , do
                P.char '|' <* P.spaces
                return Or
            , do
                P.exact "->" <* P.spaces
                return Impl ]
        right <- parseExpression <* P.spaces
        return $ ctr left right
    , do
        P.char '!' <* P.spaces
        expr <- parseExpression <* P.spaces
        return $ Not expr
    , do
        expr <- P.char '(' *> P.spaces *> parseExpression <* P.spaces <* P.char ')'
        return $ Parenthesis expr
    , do
        var <- parseVar
        return $ ExprVar var ]

parseVar :: P.Parser Var
parseVar = do
    first <- P.alpha
    rest <- P.many P.alphaNum
    return $ Var (first:rest) 

parser = parseExpression

main = do
    content <- readFile "input.txt"
    case P.runParser parser content of
        (xs, Left err) -> 
            do
                putStrLn xs
                putStrLn $ show err
        (xs, Right value) ->
            do
                putStrLn xs
                putStrLn $ show value
