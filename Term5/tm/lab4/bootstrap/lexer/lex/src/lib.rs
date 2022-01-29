#![allow(non_snake_case)]

// =============== Common Part BEGIN ================ 
pub struct Token {
    pub regex: String,
    pub expr: String,
}

impl Token {
    pub fn new(regex: String, expr: String) -> Self { Self { regex, expr } }
}

pub struct Lex {
    pub tokens: Vec<Token>,
    pub end: String,
}
// =============== Common Part END ================== 

// =============== Generated BEGIN ================== 
pub fn parse(_filename: &str) -> Lex {

    let WHITESPACE = Token::new(r"\s".to_string(), "None".to_string());
    let SECTION_SPLIT = Token::new(r"%%\n".to_string(), "Some(Token::SECTION_SPLIT)".to_string());
    let PATTERN = Token::new(r#""([^"\\]|\\[\s\S])*""#.to_string(), "Some(Token::LITERAL(s))".to_string());
    let CODE = Token::new(r#"\{([^\{\}\\]|\\[\s\S])*(\{([^\{\}\\]|\\[\s\S])*\}|([^\{\}\\]|\\[\s\S])*)*\}"#.to_string(), "Some(Token::CODE(s))".to_string());
    let PROP = Token::new(r"%[a-zA-Z0_-]+".to_string(), "Some(Token::PROP(s))".to_string());

    Lex {
        tokens: vec![
	    SECTION_SPLIT,
	    WHITESPACE,
	    PATTERN,
	    CODE,
	    PROP,
	],
        end: "Token::END".to_string(),
    }
}
// =============== Generated END ==================== 
