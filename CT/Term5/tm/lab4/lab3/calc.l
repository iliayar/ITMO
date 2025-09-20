
%end "Token::END"

%%

/\s/ {{ None }}

/[0-9]+/ {{ Some(Token::NUM(s.parse().unwrap())) }}
/[a-zA-Z_][a-zA-Z_0-9]*/ {{ Some(Token::IDENT(s)) }}

'+' {{ Some(Token::PLUS) }}
'-' {{ Some(Token::MINUS) }}
'*' {{ Some(Token::MULT) }}
'/' {{ Some(Token::DIV) }}
'(' {{ Some(Token::LPAREN) }}
')' {{ Some(Token::RPAREN) }}
';' {{ Some(Token::SEMICOLON) }}
'=' {{ Some(Token::ASSIGN) }}

%%
