%skeleton "lalr1.cc"
%require  "3.0"
%debug 
%defines 
%define api.namespace {Calc}
%define api.parser.class {CalcParser}

%code requires{
   namespace Calc {
      class CalcDriver;
      class CalcScanner;
   }

}

%parse-param { CalcScanner  &scanner  }
%parse-param { CalcDriver  &driver  }

%code{
   #include <iostream>
   #include <cstdlib>
   #include <fstream>
   #include "calc_driver.hpp"

   #undef yylex
   #define yylex scanner.yylex
}

%define api.value.type variant
%define parse.assert

%token               END    0     "end of file"
%token <std::string> IDENT
%token <int>         NUMBER
%token               PLUS
%token               MINUS
%token               MULT
%token               DIVIDE
%token               ASSIGN
%token               LPAREN
%token               RPAREN
%token               SEMICOLON

%left PLUS MINUS
%left MULT DIVIDE

%type <int> expr

%locations

%%

file : statements;

statements : END | statement statements;

statement 
    : IDENT ASSIGN expr SEMICOLON { driver.set_variable($1, $3); }
    | expr SEMICOLON { driver.print_result($1); }
    ;

expr
    : expr PLUS expr     { $$ = $1 + $3; }
    | expr MINUS expr    { $$ = $1 - $3; }
    | expr MULT expr     { $$ = $1 * $3; }
    | expr DIVIDE expr   { $$ = $1 / $3; }
    | MINUS expr         { $$ = - $2;			 }
    | NUMBER             { $$ = $1;			 }
    | IDENT              { $$ = driver.get_variable($1); }
    | LPAREN expr RPAREN { $$ = $2;			 }
    ;

%%


void 
Calc::CalcParser::error( const location_type &l, const std::string &err_message )
    {
   std::cerr << "Error: " << err_message << " at " << l << "\n";
}
