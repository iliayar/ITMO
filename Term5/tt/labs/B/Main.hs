import Grammar
import Tokens

main = do
  content <- getContents
  print $ parseFile $ scanTokens content
    -- let (File ctx res exprs) = parseFile (scanTokens content)
    --     proof = checkProof (contextToExpressions ctx) exprs
    -- case findError proof res of
    --     (Line n) -> putStrLn ("Proof is incorrect at line " ++ show (n + 1))
    --     Whole -> putStrLn "The proof does not prove the required expression"
    --     Ok -> do
    --             putStrLn $ N.showTree $ C.convert (contextToExpressions ctx) res $ PC.catProofMaybes proof
