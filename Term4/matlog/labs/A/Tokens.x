{
module Tokens where
}

%wrapper "basic"

tokens :-

  $white+                       ;
  &                             { \s -> TokenAnd }
  \|                            { \s -> TokenOr }
  "->"                          { \s -> TokenImpl }
  !                             { \s -> TokenNot }
  \(                            { \s -> TokenLParen }
  \)                            { \s -> TokenRParen }
  [A-Z][A-Z0-9']*               { \s -> TokenVar s }

{

-- The token type:
data Token = TokenAnd
           | TokenOr
           | TokenImpl
           | TokenNot
           | TokenLParen
           | TokenRParen
           | TokenVar String
           deriving (Eq,Show)

scanTokens = alexScanTokens

}
