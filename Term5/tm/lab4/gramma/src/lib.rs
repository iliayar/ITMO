#![allow(non_snake_case)]

// =============== Common Part BEGIN ================ 
#[derive(Clone, Copy)]
pub struct NonTerminal {
    pub ident: &'static str,
}

impl NonTerminal {
    pub fn new(ident: &'static str) -> Self { Self { ident } }
}

pub struct Terminal {
    pub ident: &'static str,
}

impl Terminal {
    pub fn new(ident: &'static str) -> Self { Self { ident } }
}

pub enum RightElem {
    NonTerm(NonTerminal),
    Term(Terminal),
}

pub struct Rule {
    pub nonterm: NonTerminal,
    pub right: Vec<RightElem>,
}

impl Rule {
    pub fn new(nonterm: NonTerminal, right: Vec<RightElem>) -> Self { Self { nonterm, right } }
}

pub struct Token {
    pub decl: &'static str,
}

impl Token {
    pub fn new(decl: &'static str) -> Self { Self { decl } }
}

pub struct Gramma {
    pub tokens: Vec<Token>,
    pub rules: Vec<Rule>,
    pub start: NonTerminal,
}

impl Gramma {
    pub fn new(tokens: Vec<Token>, rules: Vec<Rule>, start: NonTerminal) -> Self { Self { tokens, rules, start } }
}
// =============== Common Part END ================== 

// =============== Generated BEGIN ================== 
pub fn parse(_filename: &str) -> Gramma {


    // let mut parser = Parser::new();
    // return parser.parse(tokens);
    let E = NonTerminal::new("E");
    let T = NonTerminal::new("T");
    let F = NonTerminal::new("F");
    let PLUS = Terminal::new("PLUS");
    let MULT = Terminal::new("MULT");
    let LPAREN = Terminal::new("LPAREN");
    let RPAREN = Terminal::new("RPAREN");
    let NUM = Terminal::new("NUM");
    Gramma::new(
	vec![
	    Token::new("PLUS"),
	    Token::new("MULT"),
	    Token::new("LPAREN"),
	    Token::new("RPAREN"),
	    Token::new("NUM(String)"),
	],
	vec![
	    Rule::new(
		E,
		vec![RightElem::NonTerm(E), RightElem::Term(PLUS), RightElem::NonTerm(T)],
	    ),
	    Rule::new(
		E,
		vec![RightElem::NonTerm(T)]
	    ),
	    Rule::new(
		T,
		vec![RightElem::NonTerm(T), RightElem::Term(MULT), RightElem::NonTerm(F)],
	    ),
	    Rule::new(
		T,
		vec![RightElem::NonTerm(F)]
	    ),
	    Rule::new(
		F,
		vec![RightElem::Term(NUM)]
	    ),
	    Rule::new(
		F,
		vec![RightElem::Term(LPAREN), RightElem::NonTerm(E), RightElem::Term(RPAREN)]
	    ),
	], E)
}
// =============== Generated END ==================== 
