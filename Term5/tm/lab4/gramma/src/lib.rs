#![allow(non_snake_case)]

// =============== Common Part BEGIN ================ 
#[derive(Clone,Hash,PartialEq,Eq)]
pub struct NonTerminal {
    pub ident: String,
}

impl NonTerminal {
    pub fn new(ident: String) -> Self { Self { ident } }
}

#[derive(Clone,Hash,PartialEq,Eq)]
pub struct Terminal {
    pub ident: String,
}

impl Terminal {
    pub fn new(ident: String) -> Self { Self { ident } }
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
    pub term: Terminal,
    pub args: Option<String>,
}

impl Token {
    pub fn new(term: Terminal, args: Option<String>) -> Self { Self { term, args } }
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
    let E = NonTerminal::new("E".to_string());
    let T = NonTerminal::new("T".to_string());
    let F = NonTerminal::new("F".to_string());
    let PLUS = Terminal::new("PLUS".to_string());
    let MULT = Terminal::new("MULT".to_string());
    let LPAREN = Terminal::new("LPAREN".to_string());
    let RPAREN = Terminal::new("RPAREN".to_string());
    let NUM = Terminal::new("NUM".to_string());
    let END = Terminal::new("END".to_string());
    Gramma::new(
	vec![
	    Token::new(PLUS.clone(), None),
	    Token::new(MULT.clone(), None),
	    Token::new(LPAREN.clone(), None),
	    Token::new(RPAREN.clone(), None),
	    Token::new(NUM.clone(), Some("String".to_string())),
	    Token::new(END.clone(), None),
	],
	vec![
	    Rule::new(
		E.clone(),
		vec![RightElem::NonTerm(E.clone()), RightElem::Term(PLUS), RightElem::NonTerm(T.clone())],
	    ),
	    Rule::new(
		E.clone(),
		vec![RightElem::NonTerm(T.clone())]
	    ),
	    Rule::new(
		T.clone(),
		vec![RightElem::NonTerm(T.clone()), RightElem::Term(MULT), RightElem::NonTerm(F.clone())],
	    ),
	    Rule::new(
		T.clone(),
		vec![RightElem::NonTerm(F.clone())]
	    ),
	    Rule::new(
		F.clone(),
		vec![RightElem::Term(NUM)]
	    ),
	    Rule::new(
		F.clone(),
		vec![RightElem::Term(LPAREN), RightElem::NonTerm(E.clone()), RightElem::Term(RPAREN)]
	    ),
	], E.clone())
}
// =============== Generated END ==================== 
