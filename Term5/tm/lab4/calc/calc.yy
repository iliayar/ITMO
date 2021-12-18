
%debug

%token END "0"
%token PLUS
%token MINUS
%token MULT
%token DIV
%token LPAREN
%token RPAREN
%token "i64" NUM

%returns "i64"

%left PLUS MINUS
%left MULT DIV

%type "i64" expr 

%%

%{
let mut res = 0i64;
%}

inp : expr { res = $1; };

expr : expr PLUS expr { return $$($1 + $3); }
     | expr MINUS expr { return $$($1 - $3); }
     | expr MULT expr { return $$($1 * $3); }
     | expr DIV expr { return $$($1 / $3); }
     | MINUS expr { return $$(- $2); }
     | LPAREN expr RPAREN { return $$($2); }
     | NUM { return $$($1); }
     ;

%%

%{

return res;

%}