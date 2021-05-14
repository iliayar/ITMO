import Grammar (parseProof)
import Proof
import ProofChecker (checkProof, findError)
import qualified ProofChecker as PC
import qualified Natural as N
import qualified Converter as C

main = do
    content <- readFile "input.txt"
    --content <- return "A -> A -> O & A | (B -> C & D) -> E"
    --putStrLn content
    case parseProof content of
        (xs, Left err) -> 
            do
                putStrLn xs
                putStrLn $ show err
        (xs, Right value@(File ctx res exprs)) ->
            do
                --putStrLn xs
                --putStrLn $ show value
                let proof = checkProof (contextToExpressions ctx) exprs
                case findError proof res of
                    (Just n) -> putStrLn $ "Proof is incorrect at line " ++ (show n)
                    _ -> do
                            --putStrLn $ unlines $ map show $ proof
                            putStrLn $ N.showTree $ C.convert (contextToExpressions ctx) res $ PC.catProofMaybes proof

