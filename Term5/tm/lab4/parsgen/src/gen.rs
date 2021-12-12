use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::Write;

use gramma::{self, NonTerminal, Terminal};
use lex;


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
	};
	gen.generate_ctrl_table();
	return gen;
    }

    pub fn gen(&mut self) {
	self.gen_header();
	self.gen_token_definition();
	self.gen_parse_fun();
    }

    fn gen_header(&mut self) {
	write!(self.out, "
#![allow(non_snake_case, unused_variables, dead_code)]
use parslib::*;
	").ok();
    }

    fn gen_token_definition(&mut self) {
	write!(self.out, "
#[derive(Debug)]
pub enum Token {{
        ").ok();
	for token in self.gramma.tokens.iter() {
	    write!(self.out, "{}", token.term.ident).ok();
	    if let Some(args) = &token.args {
		writeln!(self.out, "({}),", args).ok();
	    } else {
		writeln!(self.out, ",").ok();
	    }
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
    }
}

