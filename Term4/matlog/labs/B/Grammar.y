{
module Grammar where
import Tokens
import Proof
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
    ','      { TokenComma }
    '('      { TokenLParen }
    ')'      { TokenRParen }
    var      { TokenVar $$ }

%right impl
%left or
%left and
%left not

%%

File : Context turn Expr Proof { File (if $1 == [] then EmptyContext else Context $1) $3 $4 }

Context : Expr ',' Context { $1 : $3 }
        | Expr { [$1] }
        | {- empty -} { [] }

Proof : Expr Proof { $1 : $2 }
      | {- empty -} { [] }

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
