
%end "Token::END"

%%

"\\s" { None }

"[0-9]+" { Some(Token::NUM(s.parse().unwrap())) }

"\\+" { Some(Token::PLUS) }
"-" { Some(Token::MINUS) }
"\\*" { Some(Token::MULT) }
"/" { Some(Token::DIV) }

"\\(" { Some(Token::LPAREN) }
"\\)" { Some(Token::RPAREN) }

%%
