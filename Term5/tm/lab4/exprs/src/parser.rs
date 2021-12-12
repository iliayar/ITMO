#![allow(non_snake_case, unused_variables, dead_code)]
use parslib::*;

#[derive(Debug)]
pub enum Token {
    PLUS,
    MULT,
    LPAREN,
    RPAREN,
    NUM(String),
}

pub fn parse(input: &str) {
    let mut lexems = lexer::Lexer::new();
    lexems.add(r"\+", |s| Some(Token::PLUS));
    lexems.add(r"\*", |s| Some(Token::MULT));
    lexems.add(r"\(", |s| Some(Token::LPAREN));
    lexems.add(r"\)", |s| Some(Token::RPAREN));
    lexems.add(r"[0-9]+", |s| Some(Token::NUM(s.parse().unwrap())));
    lexems.add(r"\s+", |s| None);

    let tokens = match lexems.lex(input) {
        Ok(res) => res,
        Err(lex_err) => {
            prety_print_lex_error("stdin", input, lex_err);
            panic!("Failed to lex file");
        }
    };

    println!("{:?}", tokens);
}
