
%end "Token::END"

%%

/\s/ {{ None }}
/%%\n/ {{ Some(Token::SECTION_SPLIT) }}

"\"([^\"\\\\]|\\\\[\\s\\S])*\"" {{ Some(Token::LITERAL(s)) }}
/'([^'\\]|\\[\s\S])*'/ {{ Some(Token::KEYWORD(s)) }}
/\/([^\/\\]|\\[\s\S])*\// {{ Some(Token::REGEX(s[1..s.len()-1].to_string())) }}

/\{\{(?:(?!\}\})(.|\n))+\}\}/ {{ Some(Token::CODE(s[1..s.len()-1].to_string())) }}
/%[a-zA-Z0_-]+/ {{ Some(Token::PROP(s)) }}

%%
