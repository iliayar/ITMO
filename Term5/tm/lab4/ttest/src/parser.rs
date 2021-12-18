#![allow(
    non_snake_case,
    unused_variables,
    dead_code,
    unreachable_patterns,
    unreachable_code,
    non_camel_case_types,
    unused_mut
)]
use parslib::*;

#[derive(Debug)]
pub enum Token {
    END,
}

#[derive(Debug)]
pub enum NonTerm {
    DA,
    S,
}

pub fn parse(input: &str) -> () {
    let mut lexems = lexer::Lexer::new(Token::END);

    let tokens = match lexems.lex(input) {
        Ok(res) => res,
        Err(lex_err) => {
            prety_print_lex_error("stdin", input, lex_err);
            panic!("Failed to lex file");
        }
    };

    let mut parser = parser::Parser::new(tokens, |state, nt| match state {
        0 => match nt {
            NonTerm::DA => Some(1),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        1 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        2 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        _ => unreachable!(),
    });

    while !parser.accepted() {
        parser::print_parser_state(&parser);
        match parser.state() {
            0 => match parser.lookahead() {
                Token::END => parser.shift(2),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            1 => match parser.lookahead() {
                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            2 => match parser.lookahead() {
                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            _ => parser.panic_location("<filename>", input, "Unexpected token"),
        }
    }
}
