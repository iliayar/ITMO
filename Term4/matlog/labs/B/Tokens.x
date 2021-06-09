{
module Tokens where
}

%wrapper "basic"

tokens :-

  $white+                       ;
  &                             { \s -> TokenAnd }
  \|                            { \s -> TokenOr }
  "|-"                          { \s -> TokenTurn }
  "->"                          { \s -> TokenImpl }
  !                             { \s -> TokenNot }
  \,                            { \s -> TokenComma }
  \(                            { \s -> TokenLParen }
  \)                            { \s -> TokenRParen }
  [A-Z][A-Z0-9']*               { \s -> TokenVar s }

{

-- The token type:
data Token = TokenAnd
           | TokenOr
           | TokenNewLine
           | TokenTurn
           | TokenImpl
           | TokenNot
           | TokenComma
           | TokenLParen
           | TokenRParen
           | TokenVar String
           deriving (Eq,Show)

scanTokens = alexScanTokens

}
