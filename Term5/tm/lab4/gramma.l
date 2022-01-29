
%end "Token::END"

%%

/\s/ {{ None }}

/%%\n/ {{ Some(Token::SECTION_SPLIT) }}

/[a-zA-Z_][a-zA-Z0-9_]*/ {{ Some(Token::IDENT(s)) }}

"\"([^\"\\\\]|\\\\[\\s\\S])*\"" {{ Some(Token::LITERAL(s[1..s.len()-1].to_string())) }}
/'([^'\\]|\\[\s\S])*'/ {{ Some(Token::ALIAS(s[1..s.len()-1].to_string())) }}
/%[a-zA-Z0-9_-]+/ {{ Some(Token::PROP(s)) }}

/%\{(?:(?!%\})(.|\n))+%\}/ {{ Some(Token::PLAIN_CODE(s[2..s.len()-2].to_string())) }}
/\{\{(?:(?!\}\})(.|\n))+\}\}/ {{ Some(Token::BRACKET_CODE(s[1..s.len()-1].to_string())) }}

'|' {{ Some(Token::RULE_DIV) }}
';' {{ Some(Token::SEMICOLON) }}
':' {{ Some(Token::COLON) }}

%%
