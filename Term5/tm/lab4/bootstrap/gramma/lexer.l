
%end "Token::END"

%%

"\\s" { None }

"%%\\n" { Some(Token::SECTION_SPLIT) }

"\"([^\"\\\\]|\\\\[\\s\\S])*\"" { Some(Token::LITERAL(s)) }

"%\\{(?:(?!%\\})(.|\n))+%\\}" { Some(Token::PLAIN_CODE(s[2..s.len()-2].to_string())) }

"\\{([^\\{\\}\\\\]|\\\\[\\s\\S])*(\\{([^\\{\\}\\\\]|\\\\[\\s\\S])*\\}|([^\\{\\}\\\\]|\\\\[\\s\\S])*)*\\}"
    { Some(Token::BRACKET_CODE(s)) }

"%[a-zA-Z0_-]+" { Some(Token::PROP(s)) }

"[a-zA-Z_]+" { Some(Token::IDENT(s)) }

"\\|" { Some(Token::RULE_DIV) }

";" { Some(Token::SEMICOLON) }

":" { Some(Token::COLON) }

%%

