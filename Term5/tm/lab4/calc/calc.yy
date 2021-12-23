
%token END "0"
%token PLUS
%token MINUS
%token MULT
%token DIV
%token LPAREN
%token RPAREN
%token FACTORIAL
%token SEMICOLON
%token "i64" NUM

%alias ';' SEMICOLON
%alias '!' FACTORIAL
%alias '/' DIV
%alias '*' MULT
%alias '-' MINUS
%alias '+' PLUS
%alias '(' LPAREN
%alias ')' RPAREN

%left PLUS MINUS
%left MULT DIV
%left FACTORIAL

%returns "()"

%type "i64" expr 

%%
inp : expr_line ';' inp
    |
    ;

expr_line : expr {{ println!("{}", $1); }};

expr : expr '+' expr {{ return $$($1 + $3); }}
     | expr '-' expr {{ return $$($1 - $3); }}
     | expr '*' expr {{ return $$($1 * $3); }}
     | expr '/' expr {{ return $$($1 / $3); }}
     | expr '!' {{ return $$((1..=$1).product()); }}
     | '-' expr {{ return $$(- $2); }}
     | '(' expr ')' {{ return $$($2); }}
     | NUM {{ return $$($1); }}
     ;

%%

