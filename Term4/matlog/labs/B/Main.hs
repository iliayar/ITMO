import Grammar
import Tokens
import Proof
import ProofChecker (checkProof, findError, ProofError(Line, Whole, Ok))
import qualified ProofChecker as PC
import qualified Natural as N
import qualified Converter as C

main = do
    content <- getContents
    let (File ctx res exprs) = parseFile (scanTokens content)
        proof = checkProof (contextToExpressions ctx) exprs
    case findError proof res of
        (Line n) -> putStrLn ("Proof is incorrect at line " ++ show (n + 1))
        Whole -> putStrLn "The proof does not prove the required expression"
        Ok -> do
                putStrLn $ N.showTree $ C.convert (contextToExpressions ctx) res $ PC.catProofMaybes proof
