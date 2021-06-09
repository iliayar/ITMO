module Main where
import Grammar
import Tokens
import Data
import ProofChecker
import BindingRules


main :: IO ()
main = do
    s <- getContents
    let ast = parseFile (scanTokens s)
    case annotate ast of
      (Right annotated) -> print annotated
      (Left errorAnnotated) -> print errorAnnotated
  -- let e1 = "?z.@y.y + z = z"
  --     e2 = "?x.@y.y + x = z"
  --     pe1 = parseExpr (scanTokens e1)
  --     pe2 = parseExpr (scanTokens e2)
  -- print pe1
  -- print pe2
  -- print $ findSubstitution (Var "x") pe2 pe2

