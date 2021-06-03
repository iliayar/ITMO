{
module Tokens where
}

%wrapper "basic"

$upperAlpha = [A-Z]
$lowerAlpha = [a-z]

tokens :-

  $white+                       ;
  &                             { \s -> TokenAnd }
  \|                            { \s -> TokenOr }
  \n                            { \s -> TokenNewLine }
  "|-"                          { \s -> TokenTurn }
  "->"                          { \s -> TokenImpl }
  !                             { \s -> TokenNot }
  \+                            { \s -> TokenPlus }
  \*                            { \s -> TokenTimes }
  @                             { \s -> TokenForall }
  \?                            { \s -> TokenExists }
  =                             { \s -> TokenEq }
  0                             { \s -> TokenZero }
  \(                            { \s -> TokenLParen }
  \)                            { \s -> TokenRParen }
  \.                            { \s -> TokenDot }
  [$upperAlpha]+                { \s -> TokenPred s }
  [$lowerAlpha]+                { \s -> TokenVar s }

{

-- The token type:
data Token = TokenAnd
           | TokenOr
           | TokenNewLine
           | TokenTurn
           | TokenImpl
           | TokenNot
           | TokenPlus
           | TokenTimes
           | TokenForall
           | TokenExists
           | TokenEq
           | TokenZero
           | TokenLParen
           | TokenRParen
           | TokenDot
	   | TokenVar String
	   | TokenPred String
           deriving (Eq,Show)

scanTokens = alexScanTokens

}
