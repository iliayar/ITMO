{
module Grammar where
import Tokens
import Data
}

%name parseExpr
%tokentype { Token }
%error { parseError }

%token
    and      { TokenAnd }
    or       { TokenOr }
    impl     { TokenImpl }
    not      { TokenNot }
    '('      { TokenLParen }
    ')'      { TokenRParen }
    var      { TokenVar $$ }

%right impl
%left or
%left and
%left not

%%

Expr : Expr impl Expr { Impl $1 $3 }
     | Expr or Expr { Or $1 $3 }
     | Expr and Expr { And $1 $3 }
     | '(' Expr ')' { $2 }
     | not Expr { Not $2 }
     | var { Var $1 }

{
parseError :: [Token] -> a
parseError ts = error $ "Parse error: " ++ show ts
}
