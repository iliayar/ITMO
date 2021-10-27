%{
#include <string>

#include "calc_scanner.hpp"
#undef  YY_DECL
#define YY_DECL int Calc::CalcScanner::yylex( Calc::CalcParser::semantic_type * const lval, Calc::CalcParser::location_type *loc )

using token = Calc::CalcParser::token;

#define yyterminate() return( token::END )

%}

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


