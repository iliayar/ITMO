#![allow(non_snake_case)]

use std::{collections::{HashMap, HashSet}, iter::FromIterator, hash::Hash};

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
    pub nonterms: HashSet<NonTerminal>,
    pub terms: HashSet<Terminal>,
    pub rules: Vec<Rule>,
    pub start: NonTerminal,
    pub end: Terminal,
    pub resolvs: Vec<(Terminal, Assoc, usize)>,
    pub term_type: HashMap<Terminal, String>,
    pub nonterm_type: HashMap<NonTerminal, String>,
    pub nonterm_eval: HashMap<Rule, String>,
    pub header: String,
    pub return_type: String,
    pub init_code: String,
    pub fin_code: String,
}


// =============== Common Part END ================== 

// =============== Generated BEGIN ================== 
pub fn parse(_filename: &str) -> Gramma {

    let tSECTION_SPLIT = Terminal::new("SECTION_SPLIT".to_string());
    let tLITERAL = Terminal::new("LITERAL".to_string());
    let tEND = Terminal::new("END".to_string());
    let tCODE = Terminal::new("CODE".to_string());
    let tPROP = Terminal::new("PROP".to_string());

    let ntDOC = NonTerminal::new("DOC".to_string());
    let ntSECTION1 = NonTerminal::new("SECTION1".to_string());
    let ntSECTION2 = NonTerminal::new("SECTION2".to_string());
    let ntSECTION3 = NonTerminal::new("SECTION3".to_string());
    let ntTERM = NonTerminal::new("TERM".to_string());
    let ntTERMS = NonTerminal::new("TERMS".to_string());
    let ntPROP = NonTerminal::new("PROP".to_string());
    let ntPROPS = NonTerminal::new("PROPS".to_string());

    let rDOC = Rule::new(
	ntDOC.clone(),
	vec![
	    RightElem::NonTerm(ntSECTION1.clone()),
	    RightElem::Term(tSECTION_SPLIT.clone()),
	    RightElem::NonTerm(ntSECTION2.clone()),
	    RightElem::Term(tSECTION_SPLIT.clone()),
	    RightElem::NonTerm(ntSECTION3.clone()),
	]
    );

    let rSECTION1 = Rule::new(
	ntSECTION1.clone(),
	vec![
	    RightElem::NonTerm(ntPROPS.clone()),
	]
    );

    let rSECTION2 = Rule::new(
	ntSECTION2.clone(),
	vec![
	    RightElem::NonTerm(ntTERMS.clone()),
	]
    );

    let rSECTION3 = Rule::new(
	ntSECTION3.clone(),
	vec![
	]
    );

    let rTERM = Rule::new(
	ntTERM.clone(),
	vec![
	    RightElem::Term(tLITERAL.clone()),
	    RightElem::Term(tCODE.clone()),
	]
    );

    let rTERMS1 = Rule::new(
	ntTERMS.clone(),
	vec![ ]
    );

    let rTERMS2 = Rule::new(
	ntTERMS.clone(),
	vec![
	    RightElem::NonTerm(ntTERM.clone()),
	    RightElem::NonTerm(ntTERMS.clone()),
	]
    );

    let rPROPS1 = Rule::new(
	ntPROPS.clone(),
	vec![ ]
    );

    let rPROPS2 = Rule::new(
	ntPROPS.clone(),
	vec![
	    RightElem::NonTerm(ntPROP.clone()),
	    RightElem::NonTerm(ntPROPS.clone()),
	]
    );

    let rPROP = Rule::new(
	ntPROP.clone(),
	vec![
	    RightElem::Term(tPROP.clone()),
	    RightElem::Term(tLITERAL.clone()),
	]
    );

    Gramma {
        nonterms: HashSet::from_iter(vec![
	    ntDOC.clone(),
	    ntSECTION1.clone(),
	    ntSECTION2.clone(),
	    ntSECTION3.clone(),
	    ntTERM.clone(),
	    ntTERMS.clone(),
	    ntPROP.clone(),
	    ntPROPS.clone(),
	].into_iter()),

        terms: HashSet::from_iter(vec![
	    tSECTION_SPLIT.clone(),
	    tLITERAL.clone(),
	    tCODE.clone(),
	    tEND.clone(),
	    tPROP.clone(),
	].into_iter()),

        rules: vec![
	    rDOC.clone(),
	    rSECTION1.clone(),
	    rSECTION2.clone(),
	    rSECTION3.clone(),
	    rTERM.clone(),
	    rTERMS1.clone(),
	    rTERMS2.clone(),
	    rPROP.clone(),
	    rPROPS1.clone(),
	    rPROPS2.clone(),
	],

        start: ntDOC.clone(),

        end: tEND.clone(),

        resolvs: vec![
	],

        term_type: HashMap::from_iter(vec![
	    (tLITERAL.clone(), "String".to_string()),
	    (tCODE.clone(), "String".to_string()),
	    (tPROP.clone(), "String".to_string()),
	].into_iter()),

        nonterm_type: HashMap::from_iter(vec![
	].into_iter()),

        nonterm_eval: HashMap::from_iter(vec![
	    (rTERM.clone(), r#"
{
builder.add_token(driver::lexer::Token::new($1, $2));
}
"#.to_string()),
	    (rPROP.clone(), r#"
{
match $1.as_ref() {
   "%end" => { builder.end($2.trim_matches('"').to_string()); }
   _ => { panic!("Invalid property: {}", $1); }
}
}
"#.to_string()),
	].into_iter()),

        header: "
use super::driver;
".to_string(),
        return_type: "driver::lexer::Lex".to_string(),

        init_code: "
let mut builder = driver::lexer::LexBuilder::new();
".to_string(),

        fin_code: "
return builder.build();
".to_string(),
    }
}
// =============== Generated END ==================== 
