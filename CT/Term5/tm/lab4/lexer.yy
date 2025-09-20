
%{
use super::driver;
%}


%token END "0"
%token SECTION_SPLIT
%token "String" LITERAL
%token "String" KEYWORD
%token "String" REGEX
%token "String" CODE
%token "String" PROP

%returns "driver::lexer::Lex"

%%

%{
let mut builder = driver::lexer::LexBuilder::new();
%}

doc : first_section SECTION_SPLIT second_section SECTION_SPLIT third_section ;

first_section : props ;

second_section : terms ;

third_section : ;

term : LITERAL CODE {{ builder.add_token($1, $2); }}
     | KEYWORD CODE {{ builder.add_token_keyword($1, $2); }}
     | REGEX CODE {{ builder.add_token_regex($1, $2); }}
     ;

terms :
      | term terms
      ;

props :
      | prop props
      ;

prop : PROP LITERAL {{ builder.prop($1, $2); }};

%%

%{
return builder.build();
%}