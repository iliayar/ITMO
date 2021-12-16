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

impl Lex {
    pub fn new(tokens: Vec<Token>, end: String) -> Self { Self { tokens, end } }
}
// =============== Common Part END ================== 

// =============== Generated BEGIN ================== 
pub fn parse(_filename: &str) -> Lex {
    Lex::new(
	vec![
	    Token::new(r"\+".to_string(), "Some(Token::PLUS)".to_string()),
	    Token::new(r"\*".to_string(), "Some(Token::MULT)".to_string()),
	    Token::new(r"-".to_string(), "Some(Token::MINUS)".to_string()),
	    Token::new(r"/".to_string(), "Some(Token::DIV)".to_string()),
	    Token::new(r"\(".to_string(), "Some(Token::LPAREN)".to_string()),
	    Token::new(r"\)".to_string(), "Some(Token::RPAREN)".to_string()),
	    Token::new(r"[0-9]+".to_string(), "Some(Token::NUM(s.parse().unwrap()))".to_string()),
	    Token::new(r"\s+".to_string(), "None".to_string()),
	],
	"Token::END".to_string(),
    )
}
// =============== Generated END ==================== 
