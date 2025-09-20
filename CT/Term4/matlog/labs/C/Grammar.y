{
module Grammar where
import Tokens
import Data
}

%name parseFile
%tokentype { Token }
%error { parseError }

%token
    and      { TokenAnd }
    or       { TokenOr }
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
    succ     { TokenSucc }
    pred     { TokenPred $$ }
    var      { TokenVar $$ }

%right impl
%left or
%left and
%left plus
%left times
%left not
%left succ

%%

File : Header Proof { File $1 $2 }

Header : turn Expr { $2 }

Proof : Expr Proof { $1 : $2 }
     | {- empty -} { [] }

Expr : Expr impl Expr { Impl $1 $3 }
     | Expr or Expr { Or $1 $3 }
     | Expr and Expr { And $1 $3 }
     | '(' Expr ')' { $2 }
     | not Expr { Not $2 }
     | forall Var '.' Expr { Forall $2 $4 }
     | exists Var '.' Expr { Exists $2 $4 }
     | Pred { ExprPred $1 }

Var : var { Var $1 }

Pred : Term eq Term { PredEq $1 $3 }
     | pred { Pred $1 }

Term : Term plus Term { Plus $1 $3 }
     | Term times Term { Times $1 $3 }
     | '(' Term ')' { $2 }
     | Term succ { Succ $1 }
     | zero { Zero }
     | var { TermVar $ Var $1 }
{
parseError :: [Token] -> a
parseError ts = error $ "Parse error: " ++ show ts
}
