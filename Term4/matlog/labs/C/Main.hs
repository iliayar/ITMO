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

