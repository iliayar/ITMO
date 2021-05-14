import Grammar (parseExpr)
import Proof

main = do
    content <- readFile "input.txt"
    --content <- return "A -> A -> O & A | (B -> C & D) -> E"
    --putStrLn content
    case parseExpr content of
        (xs, Left err) -> 
            do
                putStrLn xs
                putStrLn $ show err
        (xs, Right expr) ->
            do
                putStrLn $ show expr
