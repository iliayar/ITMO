{
module Tokens where
}

%wrapper "basic"

tokens :-

  $white+                       ;
  "*   "                        { \s -> TokenIndent }
  "forall"                      { \s -> TokenForall }
  "let"                         { \s -> TokenLet }
  "in"                          { \s -> TokenIn }
  \.                            { \s -> TokenDot }
  \:                            { \s -> TokenColon }
  "->"                          { \s -> TokenArrow }
  "|-"                          { \s -> TokenVdash }
  \,                            { \s -> TokenComma }
  \=                            { \s -> TokenAssign }
  \\                            { \s -> TokenLambda }
  \[rule\ \#[1-6]\]             { \s -> TokenRule $ read $ take 1 $ drop 7 $ s }
  [a-z][a-z0-9']*               { \s -> TokenVar s }
  \(                            { \s -> TokenLParen }
  \)                            { \s -> TokenRParen }

{

-- The token type:
data Token = TokenIndent
           | TokenForall
           | TokenLet
           | TokenIn
           | TokenDot
           | TokenColon
           | TokenArrow
           | TokenVdash
           | TokenComma
           | TokenAssign
           | TokenLambda
           | TokenRule Int
           | TokenVar String
	   | TokenLParen
	   | TokenRParen
            deriving (Eq,Show)

scanTokens = alexScanTokens

}
