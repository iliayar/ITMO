{
module Grammar where
import Tokens
}

%name parseCalc
%tokentype { Token }
%error { parseError }

%token
    and      { TokenAnd }
    or       { TokenOr }
    newLine  { TokenNewLine }
    turn     { TokenTurn }
    impl     { TokenImpl }
    not      { TokenNot }
    plus     { TokenPlus }
    times    { TokenTimes }
    forall   { TokenForall }
    exists   { TokenExists }
    eq       { TokenEq }
    zero     { TokenZero }
    '('      { TokenLParen }
    ')'      { TokenRParen }
    '.'      { TokenDot }
    pred     { TokenPred $$ }
    var      { TokenVar $$ }

%right impl
%left and
%left or
%left plus
%left times
%left not

%%

File : Header newLine Proof { File $1 $3 }

Header : turn Expr { $2 }

Proof : Expr newLine Proof { $1 : $3 }
      | {- empty -} { [] }

Expr : Expr impl Expr { Impl $1 $3 }
     | Expr or Expr { Or $1 $3 }
     | Expr and Expr { And $1 $3 }
     | '(' Expr ')' { $2 }
     | not Expr { Not $2 }
     | forall Var '.' Expr { Forall $2 $4 }
     | exists Var '.' Expr { Exists $2 $4 }
     | Pred { ExprPred $1 }
     | Var { ExprVar $1 }

Var : var { Var $1 }

Pred : Term eq Term { PredEq $1 $3 }
     | pred { Pred $1 }

Term : Term plus Term { Plus $1 $3 }
     | Term times Term { Times $1 $3 }
     | '(' Term ')' { $2 }
     | zero { Zero }
     | var { TermVar $1 }
{

parseError :: [Token] -> a
parseError _ = error "Parse error"

data File = File Epxr [Expr]

data Pred = Pred String | PredEq Term Term

data Term = Plus Term Term
          | Times Term Term
          | TermVar Var
          | Zero

data Var = Var String

data Expr = Impl Expr Expr
          | Or Expr Expr
          | Not Expr
          | Forall Var Expr
          | Exists Var Expr
          | ExprVar Var
          | ExprPred Pred
         deriving Show
}
