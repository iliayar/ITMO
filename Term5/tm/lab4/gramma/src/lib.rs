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
    let tBRACKET_CODE = Terminal::new("BRACKET_CODE".to_string());
    let tPROP = Terminal::new("PROP".to_string());
    let tIDENT = Terminal::new("IDENT".to_string());
    let tRULE_DIV = Terminal::new("RULE_DIV".to_string());
    let tSEMICOLON = Terminal::new("SEMICOLON".to_string());
    let tCOLON = Terminal::new("COLON".to_string());
    let tPLAIN_CODE = Terminal::new("PLAIN_CODE".to_string());

    let ntDOC = NonTerminal::new("DOC".to_string());
    let ntSECTION1 = NonTerminal::new("SECTION1".to_string());
    let ntSECTION2 = NonTerminal::new("SECTION2".to_string());
    let ntSECTION3 = NonTerminal::new("SECTION3".to_string());
    let ntPROP = NonTerminal::new("PROP".to_string());
    let ntPROP_ARGS = NonTerminal::new("PROP_ARGS".to_string());
    let ntPROPS = NonTerminal::new("PROPS".to_string());
    let ntRULE = NonTerminal::new("RULE".to_string());
    let ntRULES = NonTerminal::new("RULES".to_string());
    let ntRULE_RIGHT = NonTerminal::new("RULE_RIGHT".to_string());
    let ntRULE_RIGHT_IDENTS = NonTerminal::new("RULE_RIGHT_IDENTS".to_string());
    let ntRULE_RIGHTS = NonTerminal::new("RULE_RIGHTS".to_string());
    let ntCODE = NonTerminal::new("CODE".to_string());

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

    let rCODE1 = Rule::new(
	ntCODE.clone(),
	vec![
	    RightElem::Term(tBRACKET_CODE.clone()),
	]
    );

    let rCODE2 = Rule::new(
	ntCODE.clone(),
	vec![
	    RightElem::Term(tPLAIN_CODE.clone()),
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
	    RightElem::NonTerm(ntRULES.clone()),
	]
    );

    let rSECTION3 = Rule::new(
	ntSECTION3.clone(),
	vec![
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
	    RightElem::NonTerm(ntPROP_ARGS.clone()),
	]
    );

    let rPROP_ARGS1 = Rule::new(
	ntPROP_ARGS.clone(),
	vec![]
    );

    let rPROP_ARGS21 = Rule::new(
	ntPROP_ARGS.clone(),
	vec![
	    RightElem::NonTerm(ntPROP_ARGS.clone()),
	    RightElem::Term(tLITERAL.clone()),
	]
    );

    let rPROP_ARGS22 = Rule::new(
	ntPROP_ARGS.clone(),
	vec![
	    RightElem::NonTerm(ntPROP_ARGS.clone()),
	    RightElem::NonTerm(ntCODE.clone()),
	]
    );

    let rPROP_ARGS23 = Rule::new(
	ntPROP_ARGS.clone(),
	vec![
	    RightElem::NonTerm(ntPROP_ARGS.clone()),
	    RightElem::Term(tIDENT.clone()),
	]
    );

    let rRULES1 = Rule::new(
	ntRULES.clone(),
	vec![
	]
    );

    let rRULES2 = Rule::new(
	ntRULES.clone(),
	vec![
	    RightElem::NonTerm(ntRULE.clone()),
	    RightElem::NonTerm(ntRULES.clone()),
	]
    );

    let rRULE = Rule::new(
	ntRULE.clone(),
	vec![
	    RightElem::Term(tIDENT.clone()),
	    RightElem::Term(tCOLON.clone()),
	    RightElem::NonTerm(ntRULE_RIGHTS.clone()),
	    RightElem::Term(tSEMICOLON.clone()),
	]
    );

    let rRULE_RIGHT1 = Rule::new(
	ntRULE_RIGHT.clone(),
	vec![
	    RightElem::NonTerm(ntRULE_RIGHT_IDENTS.clone()),
	    RightElem::NonTerm(ntCODE.clone()),
	]
    );

    let rRULE_RIGHT2 = Rule::new(
	ntRULE_RIGHT.clone(),
	vec![
	    RightElem::NonTerm(ntRULE_RIGHT_IDENTS.clone()),
	]
    );

    let rRULE_RIGHT_IDENTS1 = Rule::new(
	ntRULE_RIGHT_IDENTS.clone(),
	vec![
	]
    );

    let rRULE_RIGHT_IDENTS2 = Rule::new(
	ntRULE_RIGHT_IDENTS.clone(),
	vec![
	    RightElem::NonTerm(ntRULE_RIGHT_IDENTS.clone()),
	    RightElem::Term(tIDENT.clone()),
	]
    );

    let rRULE_RIGHTS1 = Rule::new(
	ntRULE_RIGHTS.clone(),
	vec![
	    RightElem::NonTerm(ntRULE_RIGHT.clone()),
	]
    );

    let rRULE_RIGHTS2 = Rule::new(
	ntRULE_RIGHTS.clone(),
	vec![
	    RightElem::NonTerm(ntRULE_RIGHTS.clone()),
	    RightElem::Term(tRULE_DIV.clone()),
	    RightElem::NonTerm(ntRULE_RIGHT.clone()),
	]
    );

    Gramma {
        nonterms: HashSet::from_iter(vec![
	    ntDOC.clone(),
	    ntSECTION1.clone(),
	    ntSECTION2.clone(),
	    ntSECTION3.clone(),
	    ntPROP.clone(),
	    ntPROPS.clone(),
	    ntPROP_ARGS.clone(),
	    ntRULE.clone(),
	    ntRULES.clone(),
	    ntRULE_RIGHT.clone(),
	    ntRULE_RIGHTS.clone(),
	    ntRULE_RIGHT_IDENTS.clone(),
	    ntCODE.clone(),
	].into_iter()),

        terms: HashSet::from_iter(vec![
	    tSECTION_SPLIT.clone(),
	    tLITERAL.clone(),
	    tEND.clone(),
	    tPROP.clone(),
	    tIDENT.clone(),
	    tSEMICOLON.clone(),
	    tCOLON.clone(),
	    tRULE_DIV.clone(),
	    tBRACKET_CODE.clone(),
	    tPLAIN_CODE.clone(),
	].into_iter()),

        rules: vec![
	    rDOC.clone(),
	    rCODE1.clone(),
	    rCODE2.clone(),
	    rSECTION1.clone(),
	    rSECTION2.clone(),
	    rSECTION3.clone(),
	    rPROP.clone(),
	    rPROPS1.clone(),
	    rPROPS2.clone(),
	    rPROP_ARGS1.clone(),
	    rPROP_ARGS21.clone(),
	    rPROP_ARGS22.clone(),
	    rRULE.clone(),
	    rRULES1.clone(),
	    rRULES2.clone(),
	    rRULE_RIGHT1.clone(),
	    rRULE_RIGHT2.clone(),
	    rRULE_RIGHTS1.clone(),
	    rRULE_RIGHTS2.clone(),
	    rRULE_RIGHT_IDENTS1.clone(),
	    rRULE_RIGHT_IDENTS2.clone(),
	],

        start: ntDOC.clone(),

        end: tEND.clone(),

        resolvs: vec![
	],

        term_type: HashMap::from_iter(vec![
	    (tLITERAL.clone(), "String".to_string()),
	    (tPROP.clone(), "String".to_string()),
	    (tPROP.clone(), "String".to_string()),
	    (tIDENT.clone(), "String".to_string()),
	    (tBRACKET_CODE.clone(), "String".to_string()),
	    (tPLAIN_CODE.clone(), "String".to_string()),
	].into_iter()),

        nonterm_type: HashMap::from_iter(vec![
	    (ntPROP_ARGS.clone(), "Vec<String>".to_string()),
	    (ntRULE_RIGHT_IDENTS.clone(), "Vec<String>".to_string()),
	    (ntRULE_RIGHT.clone(), "(Vec<String>, Option<String>)".to_string()),
	    (ntRULE_RIGHTS.clone(), "Vec<(Vec<String>, Option<String>)>".to_string()),
	    (ntCODE.clone(), "String".to_string()),
	].into_iter()),

        nonterm_eval: HashMap::from_iter(vec![
	    (rPROP_ARGS1.clone(), r#"
{
return $$(Vec::new());
}
"#.to_string()),
	    (rPROP_ARGS21.clone(), r#"
{
$1.push($2.trim_matches('"').to_string());
return $$($1);
}
"#.to_string()),
	    (rPROP_ARGS22.clone(), r#"
{
$1.push($2);
return $$($1);
}
"#.to_string()),
	    (rPROP_ARGS23.clone(), r#"
{
$1.push($2);
return $$($1);
}
"#.to_string()),
	    (rPROP.clone(), r#"
{
gramma.add_prop($1, $2);
}
"#.to_string()),
	    (rCODE1.clone(), r#"
{
return $$($1);
}
"#.to_string()),
	    (rCODE2.clone(), r#"
{
return $$($1);
}
"#.to_string()),
	    (rRULE_RIGHT_IDENTS1.clone(), r#"
{
return $$(Vec::new());
}
"#.to_string()),
	    (rRULE_RIGHT_IDENTS2.clone(), r#"
{
$1.push($2);
return $$($1);
}
"#.to_string()),
	    (rRULE_RIGHT2.clone(), r#"
{
return $$(($1, None))
}
"#.to_string()),
	    (rRULE_RIGHT1.clone(), r#"
{
return $$(($1, Some($2)))
}
"#.to_string()),
	    (rRULE_RIGHTS1.clone(), r#"
{
return $$(vec![$1])
}
"#.to_string()),
	    (rRULE_RIGHTS2.clone(), r#"
{
$1.push($3);
return $$($1);
}
"#.to_string()),
	    (rRULE.clone(), r#"
{
gramma.add_rule_with_eval($1, $3);
}
"#.to_string()),
	].into_iter()),

        header: "
use super::driver;
".to_string(),
        return_type: "()".to_string(),

        init_code: "
let mut gramma = driver::gramma::GrammaBuilder::new();
".to_string(),

        fin_code: r#"
println!("{:?}", gramma);
return ();
"#.to_string(),
    }
}
// =============== Generated END ==================== 
