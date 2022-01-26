{
module Grammar where
import Tokens
import Proof
import qualified Data.Map as M
}

%name parseFile
%tokentype { Token }
%error { parseError }

%token
  var    { TokenVar $$ }
  rule   { TokenRule $$ }
  indent { TokenIndent }
  forall { TokenForall }
  let    { TokenLet }
  in     { TokenIn }
  '.'    { TokenDot }
  ':'    { TokenColon }
  '->'   { TokenArrow }
  '|-'   { TokenVdash }
  ','    { TokenComma }
  '='    { TokenAssign }
  lambda { TokenLambda }
  '('    { TokenLParen }
  ')'    { TokenRParen }

%left in
%right '->'

%%

File : Proof { makeTree $1 }

Proof : {- empty -} { [] }
      |	Line Proof { $1 : $2 }

Indent : {- empty -} { 0 }
       | indent Indent { 1 + $2 }

Line : Indent Context '|-' TypedExpression rule { ($1, Statement $2 $4 (Rule $5)) }

TypedExpression : Expression ':' Type { $1 ::: $3 }

Context : ContextPrime { Context $1 }

ContextPrime : {- empty -} { M.empty }
	     | var ':' Type { M.singleton (Var $1) $3 }
	     | var ':' Type ',' ContextPrime { M.insert (Var $1) $3 $5 }

Type : '(' Type ')' { $2 }
     | Monotype { TypeMonoType $1 }
     | forall var '.' Type { TypeForall (TypeVar $2) $4 }

Monotype : var { MonoTypeVar $ TypeVar $1 }
	 | '(' Monotype ')' { $2 }
	 | Monotype '->' Monotype { $1 :->: $3 }

Expression : lambda var '.' Expression { Var $2 :\: $4 }
	   | Application lambda var '.' Expression { $1 :@: Var $3 :\: $5 }
	   | let var '=' Expression in Expression { ExpressionLetIn (Var $2) $4 $6 }
	   | Application { $1 }

Application : Atom { $1 }
	    | Application Atom { $1 :@: $2 }

Atom : '(' Expression ')' { $2 }
     | var { ExpressionVar $ Var $1 }

{
parseError :: [Token] -> a
parseError ts = error $ "Parse error: " ++ show ts
}
