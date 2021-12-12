use std::fs::File;
use std::io::Write;

use gramma;
use lex;

pub struct Generator {
    // res_mod: String,
    out: std::fs::File,
    gramma: gramma::Gramma,
    lex: lex::Lex,
}

impl Generator {
    pub fn new(lex_file: &str, gramma_file: &str, out_file: &str, _res_mod: &str) -> Generator {

	let out = File::create(out_file).expect(&format!("{}: Cannot open output file", out_file));
	// let res_mod = res_mod.to_string();

	let gramma = gramma::parse(gramma_file);
	let lex = lex::parse(lex_file);

	Generator {
	    // res_mod,
	    out,
	    gramma,
	    lex,
	}
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
	let mut tokens: String = String::new();
	for token in self.gramma.tokens.iter() {
	    tokens.push_str(&format!("{},", token.decl));
	    tokens.push('\n');
	}
	write!(self.out, "
#[derive(Debug)]
pub enum Token {{
    {}
}}
        ", tokens).ok();
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
	let mut tokens = String::new();
	for token in self.lex.tokens.iter() {
	    tokens.push_str(&format!("lexems.add(r\"{}\", |s| {});", token.regex, token.expr));
	    tokens.push('\n');
	}
	write!(self.out, "
let mut lexems = lexer::Lexer::new();
{}
let tokens = match lexems.lex(input) {{
	Ok(res) => res,
	Err(lex_err) => {{
	    prety_print_lex_error(\"stdin\", input, lex_err);
	    panic!(\"Failed to lex file\");
	}},
}};

println!(\"{{:?}}\", tokens);
", tokens).ok();
    }
}

