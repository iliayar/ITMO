
%end "Token::END"

%%

"\\s" { None }
"[a-zA-Z_][a-zA-Z_0-9]*" { Some(Token::IDENTIFIER(s)) }
"\\*" { Some(Token::ASTERISK) }
";" { Some(Token::SEMICOLON) }
"," { Some(Token::COMMA) }
"\\(" { Some(Token::LPAREN) }
"\\)" { Some(Token::RPAREN) }

%%
