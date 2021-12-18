use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::Write;

// use gramma::gramma::{self, NonTerminal, Terminal, Rule, RightElem};
// use gramma::lex;
use ::gramma::*;
// use ngramma::lib::lexer;

use crate::lalr::{StateMachine, Action};


#[allow(non_snake_case)]
pub struct Generator {
    // res_mod: String,
    pub out: std::fs::File,
    pub gramma: Gramma,
    pub lex: Lex,

    pub eps_rule: HashSet<NonTerminal>,
    pub FIRST: HashMap<NonTerminal, HashSet<Terminal>>,
    pub state_machine: Option<StateMachine>,
}

impl Generator {
    pub fn new(lex_file: &str, gramma_file: &str, out_file: &str, _res_mod: &str) -> Generator {

	let out = File::create(out_file).expect(&format!("{}: Cannot open output file", out_file));
	// let res_mod = res_mod.to_string();

	let lex_input = std::fs::read_to_string(lex_file).unwrap();
	let gramma_input = std::fs::read_to_string(gramma_file).unwrap();

	let gramma = gramma::parse(&gramma_input);
	let lex = lex::parse(&lex_input);

	let mut gen = Generator {
	    // res_mod,
	    out,
	    gramma,
	    lex,

	    eps_rule: HashSet::new(),
	    FIRST: HashMap::new(),
	    state_machine: None,
	};
	gen.generate_ctrl_table();
	return gen;
    }

    pub fn gen(&mut self) {
	self.gen_header();
	self.gen_token_definition();
	self.gen_nonterm_definition();
	self.gen_parse_fun();
    }

    fn gen_header(&mut self) {
	write!(self.out, "
#![allow(non_snake_case, unused_variables, dead_code, unreachable_patterns, unreachable_code, non_camel_case_types, unused_mut)]
use parslib::*;

{}
	", self.gramma.header).ok();
    }

    fn gen_nonterm_definition(&mut self) {
	write!(self.out, "
#[derive(Debug)]
pub enum NonTerm {{
        ").ok();
	for nt in self.gramma.nonterms.iter() {
	    write!(self.out, "{}", nt.ident).ok();
	    if let Some(args) = &self.gramma.nonterm_type.get(nt) {
		writeln!(self.out, "({}),", args).ok();
	    } else {
		writeln!(self.out, ",").ok();
	    }
	}
	write!(self.out, "
}}
        ").ok();
    }

    fn gen_token_definition(&mut self) {
	write!(self.out, "
#[derive(Debug)]
pub enum Token {{
        ").ok();
	for t in self.gramma.terms.iter() {
	    write!(self.out, "{}", t.ident).ok();
	    if let Some(arg) = &self.gramma.term_type.get(t) {
		writeln!(self.out, "({})", arg).ok();
	    }
	    write!(self.out, ",").ok();
	}
	write!(self.out, "
}}
        ").ok();
    }

    fn gen_parse_fun(&mut self) {
	write!(self.out, "
pub fn parse(input: &str) -> {} {{
{}
", self.gramma.return_type, self.gramma.init_code).ok();
	self.gen_parse_fun_lex();
	write!(self.out, "
{}
}}
", self.gramma.fin_code).ok();
    }

    fn gen_parse_fun_lex(&mut self) {
	write!(self.out, "
let mut lexems = lexer::Lexer::new({});
", self.lex.end).ok();
	for token in self.lex.tokens.iter() {
	    writeln!(self.out, "lexems.add({}, |s| {});", token.regex, token.expr).ok();
	}
	write!(self.out, "
let tokens = match lexems.lex(input) {{
	Ok(res) => res,
	Err(lex_err) => {{
	    prety_print_lex_error(\"stdin\", input, lex_err);
	    panic!(\"Failed to lex file\");
	}},
}};
").ok();
	self.gen_parse_loop();
    }

    fn gen_parse_loop(&mut self) {
	let state_machine = self.state_machine.take().unwrap();
	write!(self.out, "
let mut parser = parser::Parser::new(tokens, |state, nt| {{
    match state {{
").ok();
	for (state, state_id) in state_machine.states.iter().zip(0..) {
	    write!(self.out, "
{} => match nt {{
", state_id).ok();
	    for (nt, nstate) in state.nonterm_trans.iter() {
		write!(self.out, "NonTerm::{}{} => Some({}),", nt.ident, self.get_nonterm_arg(&nt, "_"), nstate).ok();
	    }
	    write!(self.out, "
    NonTerm::{} => None,
    _ => unreachable!()
}},
", self.gramma.start.ident).ok();
	}
	write!(self.out, "
        _ => unreachable!()
    }}
}});
").ok();
	write!(self.out, "
while !parser.accepted() {{
    parser::print_parser_state(&parser);
    match parser.state() {{
").ok();
	for (state, state_id) in state_machine.states.iter().zip(0..) {
	    write!(self.out, "
{} => match parser.lookahead() {{
", state_id).ok();
	    for (t, act) in state.term_trans.iter() {
		write!(self.out, "Token::{}{} => ", t.ident, self.get_term_arg(&t, "_")).ok();
		match act {
		    Action::Shift(nstate) => {
			writeln!(self.out, "parser.shift({}),", nstate).ok();
		    },
		    Action::Reduce(rule) => {
			self.gen_reduce(rule);
		    },
		};
	    }
	    write!(self.out, "
    _ => parser.panic_location(\"<filename>\", input, \"Unexpected token\")
}},
").ok();
	}
	write!(self.out, "
        _ => parser.panic_location(\"<filename>\", input, \"Unexpected token\")
    }}
}}
").ok();
    }

    fn gen_reduce(&mut self, rule: &Rule) {
	writeln!(self.out, "parser.reduce({}, |right| {{
let mut right = right;

", rule.right.len()).ok();
	for (r, i) in rule.right.iter().zip(0..) {
	    let arg_name = format!("arg{}", i);
	    match r {
		RightElem::NonTerm(nt) => {
		    write!(self.out, "
if let parser::StackElement::NonTerminal(NonTerm::{}{}) = right.pop().unwrap() {{
", nt.ident, self.get_nonterm_arg(nt, arg_name)).ok();
		},
		RightElem::Term(t) => {
		    write!(self.out, "
if let parser::StackElement::Token(Token::{}{}) = right.pop().unwrap() {{
", t.ident, self.get_term_arg(t, format!("arg{}", i))).ok();
		},
	    }
	}
	for (r, i) in rule.right.iter().zip(0..) {
	    let arg_name = format!("arg{}", i);
	    match r {
		RightElem::NonTerm(nt) => {
		    if let Some(_) = self.gramma.nonterm_type.get(nt) {
			writeln!(self.out, "let mut {} = {};", arg_name, arg_name).ok();
		    } else {
			writeln!(self.out, "let mut {} = ();", arg_name).ok();
		    }
		},
		RightElem::Term(t) => {
		    if let Some(_) = self.gramma.term_type.get(t) {
			writeln!(self.out, "let mut {} = {};", arg_name, arg_name).ok();
		    } else {
			writeln!(self.out, "let mut {} = ();", arg_name).ok();
		    }
		},
	    }
	}
	let ident = format!("NonTerm::{}", &rule.nonterm.ident);
	writeln!(self.out, "{}", self.prepare_user_code(&ident, rule)).ok();
	let arg = format!("todo!(\"Implement for rule: {}\")", rule_to_string(rule));
	writeln!(self.out, "return {}{};", ident, self.get_nonterm_arg(&rule.nonterm, arg)).ok();
	for _ in 0..rule.right.len() {
	    writeln!(self.out, "}}").ok();
	}
	writeln!(self.out, "unreachable!();").ok();
	writeln!(self.out, "}}),").ok();
    }

    fn get_term_arg<S: AsRef<str>>(&self, t: &Terminal, name: S) -> String {
	if let Some(_) = self.gramma.term_type.get(t) {
	    format!("({})", name.as_ref())
	} else {
	    "".to_string()
	}
    }

    fn get_nonterm_arg<S: AsRef<str>>(&self, nt: &NonTerminal, name: S) -> String {
	if let Some(_) = self.gramma.nonterm_type.get(nt) {
	    format!("({})", name.as_ref())
	} else {
	    "".to_string()
	}
    }


    // fn gen_parser(&mut self) {
    // 	write!(self.out, "let mut parser").ok();
    // }

    fn prepare_user_code(&self, ident: &str, rule: &Rule) -> String {
	let n = rule.right.len();
	if let Some(code) = self.gramma.nonterm_eval.get(rule) {
	    let mut code = code.replace("$$", &ident);
	    for i in 1..n+1 {
		code = code.replace(&format!("${}", i), &format!("arg{}", i - 1));
	    }
	    return format!("{}", code);
	} else {
	    return String::new();
	}
    }
}


fn rule_to_string(rule: &Rule) -> String {
    let mut acc = String::new();
    for r in rule.right.iter() {
	acc.push(' ');
	match r {
	    RightElem::NonTerm(nt) => acc.push_str(&nt.ident),
	    RightElem::Term(t) => acc.push_str(&t.ident),
	}
    }
    return format!("{} ->{}", rule.nonterm.ident, &acc);
}
