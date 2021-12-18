
%token END "0"
%token PLUS
%token MINUS
%token MULT
%token DIV
%token LPAREN
%token RPAREN
%token "i64" NUM

%alias '/' DIV
%alias '*' MULT
%alias '-' MINUS
%alias '+' PLUS
%alias '(' LPAREN
%alias ')' RPAREN

%returns "i64"

%left PLUS MINUS
%left MULT DIV

%type "i64" expr 

%%

%{
let mut res = 0i64;
%}

inp : expr {{ res = $1; }};

expr : expr '+' expr {{ return $$($1 + $3); }}
     | expr '-' expr {{ return $$($1 - $3); }}
     | expr '*' expr {{ return $$($1 * $3); }}
     | expr '/' expr {{ return $$($1 / $3); }}
     | '-' expr {{ return $$(- $2); }}
     | '(' expr ')' {{ return $$($2); }}
     | NUM {{ return $$($1); }}
     ;

%%

%{

return res;

%}
