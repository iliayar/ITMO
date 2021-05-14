import Grammar (parseProof)
import Proof
import ProofChecker

main = do
    content <- readFile "input.txt"
    --content <- return "A -> A -> O & A | (B -> C & D) -> E"
    putStrLn content
    case parseProof content of
        (xs, Left err) -> 
            do
                putStrLn xs
                putStrLn $ show err
        (xs, Right value@(File ctx res exprs)) ->
            do
                putStrLn xs
                putStrLn $ show value
                putStrLn $ unlines $ map show $ checkProof (contextToExpressions ctx) exprs res

