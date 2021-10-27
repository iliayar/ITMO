%{
/* C++ string header, for string ops below */
#include <string>

/* Implementation of yyFlexScanner */ 
#include "calc_scanner.hpp"
#undef  YY_DECL
#define YY_DECL int Calc::CalcScanner::yylex( Calc::CalcParser::semantic_type * const lval, Calc::CalcParser::location_type *loc )

/* typedef to make the returns for the tokens shorter */
using token = Calc::CalcParser::token;

/* define yyterminate as this instead of NULL */
#define yyterminate() return( token::END )

/* msvc2010 requires that we exclude this header file. */
#define YY_NO_UNISTD_H

/* update location on matching */
#define YY_USER_ACTION loc->step(); loc->columns(yyleng);

%}

%option debug
%option nodefault
%option yyclass="Calc::CalcScanner"
%option noyywrap
%option c++

%%
%{          /** Code executed at the beginning of yylex **/
            yylval = lval;
%}

[ \t\n]                 { /* ignore whitespaces */ }

[a-zA-Z_][a-zA-Z0-9_]*  {
                           yylval->build<std::string>(yytext);
                           return token::IDENT;
                        }

[0-9]+                  {
                           yylval->build<int>(std::stoi(yytext));
                           return token::NUMBER;
                        }

"*"                     {
                           return token::MULT;
                        }

"+"                     {
                           return token::PLUS;
                        }

"-"                     {
                           return token::MINUS;
                        }

"/"                     {
                           return token::DIVIDE;
                        }

"("                     {
                           return token::LPAREN;
                        }

")"                     {
                           return token::RPAREN;
                        }

";"                     {
                           return token::SEMICOLON;
                        }

"="                     {
                           return token::ASSIGN;
                        }
%%


