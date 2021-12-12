#![allow(non_snake_case)]

// =============== Common Part BEGIN ================ 
pub struct Token {
    pub regex: &'static str,
    pub expr: &'static str,
}

impl Token {
    pub fn new(regex: &'static str, expr: &'static str) -> Self { Self { regex, expr } }
}

pub struct Lex {
    pub tokens: Vec<Token>,
}

impl Lex {
    pub fn new(tokens: Vec<Token>) -> Self { Self { tokens } }
}
// =============== Common Part END ================== 

// =============== Generated BEGIN ================== 
pub fn parse(_filename: &str) -> Lex {
    Lex::new(
	vec![
	    Token::new(r"\+", "Some(Token::PLUS)"),
	    Token::new(r"\*", "Some(Token::MULT)"),
	    Token::new(r"\(", "Some(Token::LPAREN)"),
	    Token::new(r"\)", "Some(Token::RPAREN)"),
	    Token::new(r"[0-9]+", "Some(Token::NUM(s.parse().unwrap()))"),
	    Token::new(r"\s+", "None"),
	]
    )
}
// =============== Generated END ==================== 
