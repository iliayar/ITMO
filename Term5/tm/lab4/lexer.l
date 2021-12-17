
%end "Token::END"

%%

"\\s" { None }

"%%\\n" { Some(Token::SECTION_SPLIT) }

"\"([^\"\\\\]|\\\\[\\s\\S])*\"" { Some(Token::LITERAL(s)) }

"\\{([^\\{\\}\\\\]|\\\\[\\s\\S])*(\\{([^\\{\\}\\\\]|\\\\[\\s\\S])*\\}|([^\\{\\}\\\\]|\\\\[\\s\\S])*)*\\}"
    { Some(Token::CODE(s)) }

"%[a-zA-Z0_-]+" { Some(Token::PROP(s)) }

%%

