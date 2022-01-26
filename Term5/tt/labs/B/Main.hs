import Grammar
import Tokens
import ProofChecker (check)

main = do
  content <- getContents
  let tree = parseFile $ scanTokens content
  print tree
  print $ check $ tree
