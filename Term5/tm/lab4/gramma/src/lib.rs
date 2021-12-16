#![allow(non_snake_case)]

use std::{collections::HashMap, iter::FromIterator, hash::Hash};

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

#[derive(Clone, Copy)]
pub enum Assoc {
    Left,
    Right
}

pub struct Gramma {
    pub tokens: Vec<Terminal>,
    pub rules: Vec<Rule>,
    pub start: NonTerminal,
    pub end: Terminal,
    pub resolvs: Vec<(Terminal, Assoc, usize)>,
    pub term_type: HashMap<Terminal, String>,
    pub nonterm_type: HashMap<NonTerminal, String>,
    pub nonterm_eval: HashMap<Rule, String>,
    pub init_code: String,
    pub fin_code: String,
}

impl Gramma {
    pub fn new(tokens: Vec<Terminal>, rules: Vec<Rule>, start: NonTerminal, end: Terminal, resolvs: Vec<(Terminal, Assoc, usize)>, term_type: HashMap<Terminal, String>, nonterm_type: HashMap<NonTerminal, String>, nonterm_eval: HashMap<Rule, String>, init_code: String, fin_code: String) -> Self { Self { tokens, rules, start, end, resolvs, term_type, nonterm_type, nonterm_eval, init_code, fin_code } }
}



// =============== Common Part END ================== 

// =============== Generated BEGIN ================== 
pub fn parse(_filename: &str) -> Gramma {


    let E = NonTerminal::new("E".to_string());
    let PLUS = Terminal::new("PLUS".to_string());
    let MULT = Terminal::new("MULT".to_string());
    let MINUS = Terminal::new("MINUS".to_string());
    let DIV = Terminal::new("DIV".to_string());
    let LPAREN = Terminal::new("LPAREN".to_string());
    let RPAREN = Terminal::new("RPAREN".to_string());
    let NUM = Terminal::new("NUM".to_string());
    let END = Terminal::new("END".to_string());

    let rules = vec![
	    Rule::new( // 0
		E.clone(),
		vec![RightElem::NonTerm(E.clone()), RightElem::Term(PLUS.clone()), RightElem::NonTerm(E.clone())],
	    ),
	    Rule::new( // 1
		E.clone(),
		vec![RightElem::NonTerm(E.clone()), RightElem::Term(MULT.clone()), RightElem::NonTerm(E.clone())],
	    ),
	    Rule::new( // 2
		E.clone(),
		vec![RightElem::NonTerm(E.clone()), RightElem::Term(MINUS.clone()), RightElem::NonTerm(E.clone())],
	    ),
	    Rule::new( // 3
		E.clone(),
		vec![RightElem::NonTerm(E.clone()), RightElem::Term(DIV.clone()), RightElem::NonTerm(E.clone())],
	    ),
	    Rule::new( // 4
		E.clone(),
		vec![RightElem::Term(LPAREN.clone()), RightElem::NonTerm(E.clone()), RightElem::Term(RPAREN.clone())],
	    ),
	    Rule::new( // 5
		E.clone(),
		vec![RightElem::Term(NUM.clone())]
	    ),
    ];
    Gramma::new(
	vec![
	    MULT.clone(),
	    PLUS.clone(),
	    MINUS.clone(),
	    DIV.clone(),
	    LPAREN.clone(),
	    RPAREN.clone(),
	    NUM.clone(),
	    END.clone(),
	], rules.clone(), E.clone(), END.clone(),
	vec![
	    (PLUS.clone(), Assoc::Left, 1),
	    (MINUS.clone(), Assoc::Left, 1),
	    (MULT.clone(), Assoc::Left, 0),
	    (DIV.clone(), Assoc::Left, 0),
	],
	HashMap::from_iter(vec![
	    (NUM.clone(), "i64".to_string()),
	].into_iter()),
	HashMap::from_iter(vec![
	    (E.clone(), "i64".to_string()),
	].into_iter()),
	HashMap::from_iter(vec![
	    (rules[0].clone(), "return $$($1 + $3)".to_string()),
	    (rules[1].clone(), "return $$($1 * $3)".to_string()),
	    (rules[2].clone(), "return $$($1 - $3)".to_string()),
	    (rules[3].clone(), "return $$($1 / $3)".to_string()),
	    (rules[4].clone(), "return $$($2)".to_string()),
	    (rules[5].clone(), "return $$($1)".to_string()),
	].into_iter()),
	"
".to_string(),
	"
".to_string())

}
// =============== Generated END ==================== 
