module Main where
import Grammar
import Tokens
import Data


main :: IO ()
main = do
    s <- getContents
    let tokens = scanTokens s
        ast = parseFile (scanTokens s)
    -- print tokens
    print ast
    -- print (run ast)

