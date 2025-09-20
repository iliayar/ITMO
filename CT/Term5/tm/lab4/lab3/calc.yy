
%{
use super::driver;
%}


%token END "0"
%token ASSIGN
%token PLUS
%token MINUS
%token MULT
%token DIV
%token LPAREN
%token RPAREN
%token SEMICOLON
%token "i64" NUM
%token "String" IDENT

%alias '/' DIV
%alias '=' ASSIGN
%alias '*' MULT
%alias '-' MINUS
%alias '+' PLUS
%alias '(' LPAREN
%alias ')' RPAREN
%alias ';' SEMICOLON

%returns "()"

%left PLUS MINUS
%left MULT DIV

%type "i64" expr 

%%

%{
let mut driver = driver::CalcDriver::new();
%}

input : statement ';' input
      |
      ;

statement : expr {{ driver.eval($1); }}
	  | IDENT '=' expr {{ driver.set($1, $3); }}
	  ;

expr : expr '+' expr {{ return $$($1 + $3); }}
     | expr '-' expr {{ return $$($1 - $3); }}
     | expr '*' expr {{ return $$($1 * $3); }}
     | expr '/' expr {{ return $$($1 / $3); }}
     | '-' expr {{ return $$(- $2); }}
     | '(' expr ')' {{ return $$($2); }}
     | NUM {{ return $$($1); }}
     | IDENT {{ return $$(driver.get($1)); }}
     ;

%%
