use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::Write;

use gramma::{self, NonTerminal, Terminal, Rule, RightElem};
use lex;

use crate::lalr::{StateMachine, Action};


#[allow(non_snake_case)]
pub struct Generator {
    // res_mod: String,
    pub out: std::fs::File,
    pub gramma: gramma::Gramma,
    pub lex: lex::Lex,

    pub terms: HashSet<Terminal>,
    pub nonterms: HashSet<NonTerminal>,
    pub eps_rule: HashSet<NonTerminal>,
    pub FIRST: HashMap<NonTerminal, HashSet<Terminal>>,
    pub FOLLOW: HashMap<NonTerminal, HashSet<Terminal>>,
    pub state_machine: Option<StateMachine>,
}

impl Generator {
    pub fn new(lex_file: &str, gramma_file: &str, out_file: &str, _res_mod: &str) -> Generator {

	let out = File::create(out_file).expect(&format!("{}: Cannot open output file", out_file));
	// let res_mod = res_mod.to_string();

	let gramma = gramma::parse(gramma_file);
	let lex = lex::parse(lex_file);

	let mut gen = Generator {
	    // res_mod,
	    out,
	    gramma,
	    lex,

	    terms: HashSet::new(),
	    nonterms: HashSet::new(),
	    eps_rule: HashSet::new(),
	    FIRST: HashMap::new(),
	    FOLLOW: HashMap::new(),
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
#![allow(non_snake_case, unused_variables, dead_code, unreachable_patterns)]
use parslib::*;
	").ok();
    }

    fn gen_nonterm_definition(&mut self) {
	write!(self.out, "
#[derive(Debug)]
pub enum NonTerm {{
        ").ok();
	for nt in self.nonterms.iter() {
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
	for t in self.gramma.tokens.iter() {
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
pub fn parse(input: &str) {{
").ok();
	self.gen_parse_fun_lex();
	write!(self.out, "
}}
").ok();
    }

    fn gen_parse_fun_lex(&mut self) {
	write!(self.out, "
let mut lexems = lexer::Lexer::new({});
", self.lex.end).ok();
	for token in self.lex.tokens.iter() {
	    writeln!(self.out, "lexems.add(r\"{}\", |s| {});", token.regex, token.expr).ok();
	}
	write!(self.out, "
let tokens = match lexems.lex(input) {{
	Ok(res) => res,
	Err(lex_err) => {{
	    prety_print_lex_error(\"stdin\", input, lex_err);
	    panic!(\"Failed to lex file\");
	}},
}};

println!(\"{{:?}}\", tokens);
").ok();
	self.gen_parse_loop();
    }

    fn gen_parse_loop(&mut self) {
	let state_machine = self.state_machine.take().unwrap();
	write!(self.out, "
let mut parser = parser::Parser::<Token, NonTerm, Vec<Token>>::new(tokens, |state, nt| {{
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
    _ => unreachable!()
}},
").ok();
	}
	write!(self.out, "
        _ => panic!(\"Ooops...\")
    }}
}}
").ok();
    }

    fn gen_reduce(&mut self, rule: &Rule) {
	writeln!(self.out, "parser.reduce({}, |right| {{", rule.right.len()).ok();
	for (r, i) in rule.right.iter().zip(0..) {
	    match r {
		RightElem::NonTerm(nt) => {
		    write!(self.out, "
if let parser::StackElement::NonTerminal(NonTerm::{}{}) = right[{}] {{
", nt.ident, self.get_nonterm_arg(nt, format!("arg{}", i)), i).ok();
		},
		RightElem::Term(t) => {
		    write!(self.out, "
if let parser::StackElement::Token(Token::{}{}) = right[{}] {{
", t.ident, self.get_term_arg(t, format!("arg{}", i)), i).ok();
		},
	    }
	}
	writeln!(self.out, "return NonTerm::{}{};",
		 rule.nonterm.ident,
		 self.get_nonterm_arg(&rule.nonterm, "todo!()")).ok();
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
}

