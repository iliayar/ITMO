import Grammar (parseProof)
import Proof
import ProofChecker

checkAxioms :: [Expression] -> [(Bool, Expression)]
checkAxioms = map checkAxiom
    where checkAxiom e = (axiom e, e) 


main = do
    content <- readFile "input.txt"
    --content <- return "A -> A -> O & A | (B -> C & D) -> E"
    putStrLn content
    case parseProof content of
        (xs, Left err) -> 
            do
                putStrLn xs
                putStrLn $ show err
        (xs, Right value@(File _ _ exprs)) ->
            do
                putStrLn xs
                putStrLn $ show value
                putStrLn $ unlines $ map show $ checkAxioms exprs

