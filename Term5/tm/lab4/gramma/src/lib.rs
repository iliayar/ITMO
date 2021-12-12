#![allow(non_snake_case)]

// =============== Common Part BEGIN ================ 
#[derive(Clone,Hash,PartialEq,Eq,Debug)]
pub struct NonTerminal {
    pub ident: String,
}

impl NonTerminal {
    pub fn new(ident: String) -> Self { Self { ident } }
}

#[derive(Clone,Hash,PartialEq,Eq,Debug)]
pub struct Terminal {
    pub ident: String,
}

impl Terminal {
    pub fn new(ident: String) -> Self { Self { ident } }
}

#[derive(Clone,Hash,PartialEq,Eq,Debug)]
pub enum RightElem {
    NonTerm(NonTerminal),
    Term(Terminal),
}

#[derive(Clone,Hash,PartialEq,Eq,Debug)]
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

#[derive(Clone, Copy)]
pub enum Assoc {
    Left,
    Right
}

pub struct Gramma {
    pub tokens: Vec<Token>,
    pub rules: Vec<Rule>,
    pub start: NonTerminal,
    pub end: Terminal,
    pub resolvs: Vec<(Terminal, Assoc, usize)>
}

impl Gramma {
    pub fn new(tokens: Vec<Token>, rules: Vec<Rule>, start: NonTerminal, end: Terminal, resolvs: Vec<(Terminal, Assoc, usize)>) -> Self { Self { tokens, rules, start, end, resolvs } }
}
// =============== Common Part END ================== 

// =============== Generated BEGIN ================== 
pub fn parse(_filename: &str) -> Gramma {


    // let mut parser = Parser::new();
    // return parser.parse(tokens);

    // Simple expressions
    // let E = NonTerminal::new("E".to_string());
    // let T = NonTerminal::new("T".to_string());
    // let F = NonTerminal::new("F".to_string());
    // let PLUS = Terminal::new("PLUS".to_string());
    // let MULT = Terminal::new("MULT".to_string());
    // let LPAREN = Terminal::new("LPAREN".to_string());
    // let RPAREN = Terminal::new("RPAREN".to_string());
    // let NUM = Terminal::new("NUM".to_string());
    // let END = Terminal::new("END".to_string());
    // Gramma::new(
    // 	vec![
    // 	    Token::new(PLUS.clone(), None),
    // 	    Token::new(MULT.clone(), None),
    // 	    Token::new(LPAREN.clone(), None),
    // 	    Token::new(RPAREN.clone(), None),
    // 	    Token::new(NUM.clone(), Some("String".to_string())),
    // 	    Token::new(END.clone(), None),
    // 	],
    // 	vec![
    // 	    Rule::new(
    // 		E.clone(),
    // 		vec![RightElem::NonTerm(E.clone()), RightElem::Term(PLUS), RightElem::NonTerm(T.clone())],
    // 	    ),
    // 	    Rule::new(
    // 		E.clone(),
    // 		vec![RightElem::NonTerm(T.clone())]
    // 	    ),
    // 	    Rule::new(
    // 		T.clone(),
    // 		vec![RightElem::NonTerm(T.clone()), RightElem::Term(MULT), RightElem::NonTerm(F.clone())],
    // 	    ),
    // 	    Rule::new(
    // 		T.clone(),
    // 		vec![RightElem::NonTerm(F.clone())]
    // 	    ),
    // 	    Rule::new(
    // 		F.clone(),
    // 		vec![RightElem::Term(NUM)]
    // 	    ),
    // 	    Rule::new(
    // 		F.clone(),
    // 		vec![RightElem::Term(LPAREN), RightElem::NonTerm(E.clone()), RightElem::Term(RPAREN)]
    // 	    ),
    // 	], E.clone(), END.clone(), vec![])

    // C Function delcaration
    // let LPAREN = Terminal::new("LPAREN".to_string());
    // let RPAREN = Terminal::new("RPAREN".to_string());
    // let ASTERISK = Terminal::new("ASTERISK".to_string());
    // let COMMA = Terminal::new("COMMA".to_string());
    // let SEMICOLON = Terminal::new("SEMICOLON".to_string());
    // let IDENTIFIER = Terminal::new("IDENTIFIER".to_string());
    // let END = Terminal::new("END".to_string());
    // let DECLARATION = NonTerminal::new("DECLARATION".to_string());
    // let ARGS = NonTerminal::new("ARGS".to_string());
    // let ARGS_REST = NonTerminal::new("ARGS_REST".to_string());
    // let ARG = NonTerminal::new("ARG".to_string());
    // let POINTER = NonTerminal::new("POINTER".to_string());
    // Gramma::new(
    // 	vec![
    // 	    Token::new(LPAREN.clone(), None),
    // 	    Token::new(RPAREN.clone(), None),
    // 	    Token::new(ASTERISK.clone(), None),
    // 	    Token::new(COMMA.clone(), None),
    // 	    Token::new(SEMICOLON.clone(), None),
    // 	    Token::new(IDENTIFIER.clone(), Some("String".to_string())),
    // 	    Token::new(END.clone(), None),
    // 	],
    // 	vec![
    // 	    Rule::new(
    // 		DECLARATION.clone(),
    // 		vec![
    // 		    RightElem::Term(IDENTIFIER.clone()),
    // 		    RightElem::Term(IDENTIFIER.clone()),
    // 		    RightElem::Term(LPAREN.clone()),
    // 		    RightElem::NonTerm(ARGS.clone()),
    // 		    RightElem::Term(RPAREN.clone()),
    // 		    RightElem::Term(SEMICOLON.clone()),
    // 		],
    // 	    ),
    // 	    Rule::new(
    // 		ARGS.clone(),
    // 		vec![RightElem::NonTerm(ARG.clone()), RightElem::NonTerm(ARGS_REST.clone())]
    // 	    ),
    // 	    Rule::new(
    // 		ARGS.clone(),
    // 		vec![]
    // 	    ),
    // 	    Rule::new(
    // 		ARGS_REST.clone(),
    // 		vec![RightElem::Term(COMMA.clone()), RightElem::NonTerm(ARG.clone()), RightElem::NonTerm(ARGS_REST.clone())]
    // 	    ),
    // 	    Rule::new(
    // 		ARGS_REST.clone(),
    // 		vec![]
    // 	    ),
    // 	    Rule::new(
    // 		ARG.clone(),
    // 		vec![RightElem::Term(IDENTIFIER.clone()), RightElem::NonTerm(POINTER.clone()), RightElem::Term(IDENTIFIER.clone())]
    // 	    ),
    // 	    Rule::new(
    // 		POINTER.clone(),
    // 		vec![RightElem::Term(ASTERISK.clone()), RightElem::NonTerm(POINTER.clone())]
    // 	    ),
    // 	    Rule::new(
    // 		POINTER.clone(),
    // 		vec![]
    // 	    ),
    // 	], DECLARATION.clone(), END.clone(), vec![])

    // Expressions with conflicts
    let E = NonTerminal::new("E".to_string());
    let PLUS = Terminal::new("PLUS".to_string());
    let MULT = Terminal::new("MULT".to_string());
    let LPAREN = Terminal::new("LPAREN".to_string());
    let RPAREN = Terminal::new("RPAREN".to_string());
    let NUM = Terminal::new("NUM".to_string());
    let END = Terminal::new("END".to_string());
    Gramma::new(
	vec![
	    Token::new(MULT.clone(), None),
	    Token::new(PLUS.clone(), None),
	    Token::new(LPAREN.clone(), None),
	    Token::new(RPAREN.clone(), None),
	    Token::new(NUM.clone(), Some("String".to_string())),
	    Token::new(END.clone(), None),
	],
	vec![
	    Rule::new(
		E.clone(),
		vec![RightElem::NonTerm(E.clone()), RightElem::Term(PLUS.clone()), RightElem::NonTerm(E.clone())],
	    ),
	    Rule::new(
		E.clone(),
		vec![RightElem::NonTerm(E.clone()), RightElem::Term(MULT.clone()), RightElem::NonTerm(E.clone())],
	    ),
	    Rule::new(
		E.clone(),
		vec![RightElem::Term(LPAREN.clone()), RightElem::NonTerm(E.clone()), RightElem::Term(RPAREN.clone())],
	    ),
	    Rule::new(
		E.clone(),
		vec![RightElem::Term(NUM)]
	    ),
	], E.clone(), END.clone(),
	vec![
	    (PLUS.clone(), Assoc::Left, 1),
	    (MULT.clone(), Assoc::Right, 0),
	])

}
// =============== Generated END ==================== 
