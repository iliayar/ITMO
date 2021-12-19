#![allow(
    non_snake_case,
    unused_variables,
    dead_code,
    unreachable_patterns,
    unreachable_code,
    non_camel_case_types,
    unused_mut
)]
use super::parslib::*;
use std::io::BufRead;

use super::driver;

#[derive(Debug)]
pub enum Token {
    RPAREN,
    MINUS,
    PLUS,
    SEMICOLON,
    ASSIGN,
    DIV,
    END,
    NUM(i64),
    IDENT(String),
    LPAREN,
    MULT,
}

#[derive(Debug)]
pub enum NonTerm {
    expr(i64),
    statement,
    input,
    S,
}

pub fn get_lexems() -> lexer::Lexer<Token> {
    let mut lexems = lexer::Lexer::new(Token::END);
    lexems.add("\\s", |s| None);
    lexems.add("[0-9]+", |s| Some(Token::NUM(s.parse().unwrap())));
    lexems.add("[a-zA-Z_][a-zA-Z_0-9]*", |s| Some(Token::IDENT(s)));
    lexems.add("\\+", |s| Some(Token::PLUS));
    lexems.add("-", |s| Some(Token::MINUS));
    lexems.add("\\*", |s| Some(Token::MULT));
    lexems.add("/", |s| Some(Token::DIV));
    lexems.add("\\(", |s| Some(Token::LPAREN));
    lexems.add("\\)", |s| Some(Token::RPAREN));
    lexems.add(";", |s| Some(Token::SEMICOLON));
    lexems.add("=", |s| Some(Token::ASSIGN));

    return lexems;
}

pub fn parse_stream<R: BufRead>(filename: &str, stream: &mut R) -> () {
    let lexems = get_lexems();

    let tokens = lexems.lex_stream(stream, |lex_err, input| {
        prety_print_lex_error(filename, &input, lex_err);
        panic!("Failed to lex file");
    });

    return parse_token_stream(filename, tokens);
}

pub fn parse(filename: &str, input: &str) -> () {
    let lexems = get_lexems();

    let tokens = lexems.lex(input);

    if let Err(lex_err) = tokens {
        prety_print_lex_error(filename, &input, lex_err);
        panic!("Failed to lex file");
    } else {
        return parse_token_stream(filename, tokens.unwrap());
    }
}

pub fn parse_file(filename: &str) -> () {
    let input = std::fs::read_to_string(filename).expect("Failed to read file");

    return parse(filename, &input);
}

fn parse_token_stream<TS: parser::TokenStream<Token>>(filename: &str, tokens: TS) -> () {
    let mut driver = driver::CalcDriver::new();

    let mut parser = parser::Parser::new(tokens, |state, nt| match state {
        0 => match nt {
            NonTerm::input => Some(3),
            NonTerm::expr(_) => Some(1),
            NonTerm::statement => Some(2),
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

        3 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        4 => match nt {
            NonTerm::expr(_) => Some(19),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        5 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        6 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        7 => match nt {
            NonTerm::expr(_) => Some(8),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        8 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        9 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        10 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        11 => match nt {
            NonTerm::expr(_) => Some(18),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        12 => match nt {
            NonTerm::expr(_) => Some(17),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        13 => match nt {
            NonTerm::expr(_) => Some(16),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        14 => match nt {
            NonTerm::expr(_) => Some(15),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        15 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        16 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        17 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        18 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        19 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        20 => match nt {
            NonTerm::expr(_) => Some(21),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        21 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        22 => match nt {
            NonTerm::expr(_) => Some(1),
            NonTerm::input => Some(23),
            NonTerm::statement => Some(2),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        23 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        _ => unreachable!(),
    });

    while !parser.accepted() {
        match parser.state() {
            0 => match parser.lookahead() {
                Token::LPAREN => parser.shift(7),
                Token::MINUS => parser.shift(4),
                Token::IDENT(_) => parser.shift(6),
                Token::NUM(_) => parser.shift(5),
                Token::END => parser.reduce(0, |right| {
                    let mut right = right;

                    return NonTerm::input;
                    unreachable!();
                }),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            1 => match parser.lookahead() {
                Token::MINUS => parser.shift(11),
                Token::MULT => parser.shift(14),
                Token::DIV => parser.shift(13),
                Token::SEMICOLON => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        let mut arg0 = arg0;
                        {
                            driver.eval(arg0);
                        }
                        return NonTerm::statement;
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.shift(12),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            2 => match parser.lookahead() {
                Token::SEMICOLON => parser.shift(22),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            3 => match parser.lookahead() {
                Token::END => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::input) = right.pop().unwrap()
                    {
                        let mut arg0 = ();

                        return NonTerm::S;
                    }
                    unreachable!();
                }),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            4 => match parser.lookahead() {
                Token::LPAREN => parser.shift(7),
                Token::IDENT(_) => parser.shift(9),
                Token::NUM(_) => parser.shift(5),
                Token::MINUS => parser.shift(4),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            5 => match parser.lookahead() {
                Token::SEMICOLON => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::NUM(arg0)) = right.pop().unwrap() {
                        let mut arg0 = arg0;
                        {
                            return NonTerm::expr(arg0);
                        }
                        return NonTerm::expr(todo!("Implement for rule: expr -> NUM"));
                    }
                    unreachable!();
                }),
                Token::DIV => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::NUM(arg0)) = right.pop().unwrap() {
                        let mut arg0 = arg0;
                        {
                            return NonTerm::expr(arg0);
                        }
                        return NonTerm::expr(todo!("Implement for rule: expr -> NUM"));
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::NUM(arg0)) = right.pop().unwrap() {
                        let mut arg0 = arg0;
                        {
                            return NonTerm::expr(arg0);
                        }
                        return NonTerm::expr(todo!("Implement for rule: expr -> NUM"));
                    }
                    unreachable!();
                }),
                Token::MINUS => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::NUM(arg0)) = right.pop().unwrap() {
                        let mut arg0 = arg0;
                        {
                            return NonTerm::expr(arg0);
                        }
                        return NonTerm::expr(todo!("Implement for rule: expr -> NUM"));
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::NUM(arg0)) = right.pop().unwrap() {
                        let mut arg0 = arg0;
                        {
                            return NonTerm::expr(arg0);
                        }
                        return NonTerm::expr(todo!("Implement for rule: expr -> NUM"));
                    }
                    unreachable!();
                }),
                Token::MULT => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::NUM(arg0)) = right.pop().unwrap() {
                        let mut arg0 = arg0;
                        {
                            return NonTerm::expr(arg0);
                        }
                        return NonTerm::expr(todo!("Implement for rule: expr -> NUM"));
                    }
                    unreachable!();
                }),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            6 => match parser.lookahead() {
                Token::MULT => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {
                        let mut arg0 = arg0;
                        {
                            return NonTerm::expr(driver.get(arg0));
                        }
                        return NonTerm::expr(todo!("Implement for rule: expr -> IDENT"));
                    }
                    unreachable!();
                }),
                Token::SEMICOLON => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {
                        let mut arg0 = arg0;
                        {
                            return NonTerm::expr(driver.get(arg0));
                        }
                        return NonTerm::expr(todo!("Implement for rule: expr -> IDENT"));
                    }
                    unreachable!();
                }),
                Token::ASSIGN => parser.shift(20),
                Token::MINUS => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {
                        let mut arg0 = arg0;
                        {
                            return NonTerm::expr(driver.get(arg0));
                        }
                        return NonTerm::expr(todo!("Implement for rule: expr -> IDENT"));
                    }
                    unreachable!();
                }),
                Token::DIV => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {
                        let mut arg0 = arg0;
                        {
                            return NonTerm::expr(driver.get(arg0));
                        }
                        return NonTerm::expr(todo!("Implement for rule: expr -> IDENT"));
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {
                        let mut arg0 = arg0;
                        {
                            return NonTerm::expr(driver.get(arg0));
                        }
                        return NonTerm::expr(todo!("Implement for rule: expr -> IDENT"));
                    }
                    unreachable!();
                }),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            7 => match parser.lookahead() {
                Token::MINUS => parser.shift(4),
                Token::IDENT(_) => parser.shift(9),
                Token::NUM(_) => parser.shift(5),
                Token::LPAREN => parser.shift(7),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            8 => match parser.lookahead() {
                Token::RPAREN => parser.shift(10),
                Token::PLUS => parser.shift(12),
                Token::MINUS => parser.shift(11),
                Token::MULT => parser.shift(14),
                Token::DIV => parser.shift(13),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            9 => match parser.lookahead() {
                Token::MINUS => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {
                        let mut arg0 = arg0;
                        {
                            return NonTerm::expr(driver.get(arg0));
                        }
                        return NonTerm::expr(todo!("Implement for rule: expr -> IDENT"));
                    }
                    unreachable!();
                }),
                Token::SEMICOLON => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {
                        let mut arg0 = arg0;
                        {
                            return NonTerm::expr(driver.get(arg0));
                        }
                        return NonTerm::expr(todo!("Implement for rule: expr -> IDENT"));
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {
                        let mut arg0 = arg0;
                        {
                            return NonTerm::expr(driver.get(arg0));
                        }
                        return NonTerm::expr(todo!("Implement for rule: expr -> IDENT"));
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {
                        let mut arg0 = arg0;
                        {
                            return NonTerm::expr(driver.get(arg0));
                        }
                        return NonTerm::expr(todo!("Implement for rule: expr -> IDENT"));
                    }
                    unreachable!();
                }),
                Token::DIV => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {
                        let mut arg0 = arg0;
                        {
                            return NonTerm::expr(driver.get(arg0));
                        }
                        return NonTerm::expr(todo!("Implement for rule: expr -> IDENT"));
                    }
                    unreachable!();
                }),
                Token::MULT => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {
                        let mut arg0 = arg0;
                        {
                            return NonTerm::expr(driver.get(arg0));
                        }
                        return NonTerm::expr(todo!("Implement for rule: expr -> IDENT"));
                    }
                    unreachable!();
                }),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            10 => match parser.lookahead() {
                Token::DIV => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LPAREN) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::expr(arg1)) =
                            right.pop().unwrap()
                        {
                            if let parser::StackElement::Token(Token::RPAREN) = right.pop().unwrap()
                            {
                                let mut arg0 = ();
                                let mut arg1 = arg1;
                                let mut arg2 = ();
                                {
                                    return NonTerm::expr(arg1);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> LPAREN expr RPAREN"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::SEMICOLON => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LPAREN) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::expr(arg1)) =
                            right.pop().unwrap()
                        {
                            if let parser::StackElement::Token(Token::RPAREN) = right.pop().unwrap()
                            {
                                let mut arg0 = ();
                                let mut arg1 = arg1;
                                let mut arg2 = ();
                                {
                                    return NonTerm::expr(arg1);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> LPAREN expr RPAREN"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LPAREN) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::expr(arg1)) =
                            right.pop().unwrap()
                        {
                            if let parser::StackElement::Token(Token::RPAREN) = right.pop().unwrap()
                            {
                                let mut arg0 = ();
                                let mut arg1 = arg1;
                                let mut arg2 = ();
                                {
                                    return NonTerm::expr(arg1);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> LPAREN expr RPAREN"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LPAREN) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::expr(arg1)) =
                            right.pop().unwrap()
                        {
                            if let parser::StackElement::Token(Token::RPAREN) = right.pop().unwrap()
                            {
                                let mut arg0 = ();
                                let mut arg1 = arg1;
                                let mut arg2 = ();
                                {
                                    return NonTerm::expr(arg1);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> LPAREN expr RPAREN"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MULT => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LPAREN) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::expr(arg1)) =
                            right.pop().unwrap()
                        {
                            if let parser::StackElement::Token(Token::RPAREN) = right.pop().unwrap()
                            {
                                let mut arg0 = ();
                                let mut arg1 = arg1;
                                let mut arg2 = ();
                                {
                                    return NonTerm::expr(arg1);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> LPAREN expr RPAREN"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MINUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LPAREN) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::expr(arg1)) =
                            right.pop().unwrap()
                        {
                            if let parser::StackElement::Token(Token::RPAREN) = right.pop().unwrap()
                            {
                                let mut arg0 = ();
                                let mut arg1 = arg1;
                                let mut arg2 = ();
                                {
                                    return NonTerm::expr(arg1);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> LPAREN expr RPAREN"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            11 => match parser.lookahead() {
                Token::MINUS => parser.shift(4),
                Token::LPAREN => parser.shift(7),
                Token::NUM(_) => parser.shift(5),
                Token::IDENT(_) => parser.shift(9),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            12 => match parser.lookahead() {
                Token::IDENT(_) => parser.shift(9),
                Token::MINUS => parser.shift(4),
                Token::NUM(_) => parser.shift(5),
                Token::LPAREN => parser.shift(7),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            13 => match parser.lookahead() {
                Token::MINUS => parser.shift(4),
                Token::NUM(_) => parser.shift(5),
                Token::IDENT(_) => parser.shift(9),
                Token::LPAREN => parser.shift(7),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            14 => match parser.lookahead() {
                Token::IDENT(_) => parser.shift(9),
                Token::LPAREN => parser.shift(7),
                Token::MINUS => parser.shift(4),
                Token::NUM(_) => parser.shift(5),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            15 => match parser.lookahead() {
                Token::MULT => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MULT) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 * arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr MULT expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::SEMICOLON => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MULT) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 * arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr MULT expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::DIV => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MULT) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 * arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr MULT expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MULT) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 * arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr MULT expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MINUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MULT) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 * arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr MULT expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MULT) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 * arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr MULT expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            16 => match parser.lookahead() {
                Token::PLUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::DIV) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 / arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr DIV expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MULT => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::DIV) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 / arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr DIV expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::SEMICOLON => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::DIV) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 / arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr DIV expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::DIV) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 / arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr DIV expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MINUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::DIV) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 / arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr DIV expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::DIV => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::DIV) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 / arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr DIV expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            17 => match parser.lookahead() {
                Token::SEMICOLON => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::PLUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 + arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr PLUS expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MINUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::PLUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 + arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr PLUS expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::PLUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 + arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr PLUS expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::DIV => parser.shift(13),
                Token::RPAREN => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::PLUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 + arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr PLUS expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MULT => parser.shift(14),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            18 => match parser.lookahead() {
                Token::DIV => parser.shift(13),
                Token::RPAREN => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MINUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 - arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr MINUS expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::SEMICOLON => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MINUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 - arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr MINUS expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MINUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 - arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr MINUS expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MINUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MINUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    return NonTerm::expr(arg0 - arg2);
                                }
                                return NonTerm::expr(todo!(
                                    "Implement for rule: expr -> expr MINUS expr"
                                ));
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MULT => parser.shift(14),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            19 => match parser.lookahead() {
                Token::SEMICOLON => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::MINUS) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::expr(arg1)) =
                            right.pop().unwrap()
                        {
                            let mut arg0 = ();
                            let mut arg1 = arg1;
                            {
                                return NonTerm::expr(-arg1);
                            }
                            return NonTerm::expr(todo!("Implement for rule: expr -> MINUS expr"));
                        }
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::MINUS) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::expr(arg1)) =
                            right.pop().unwrap()
                        {
                            let mut arg0 = ();
                            let mut arg1 = arg1;
                            {
                                return NonTerm::expr(-arg1);
                            }
                            return NonTerm::expr(todo!("Implement for rule: expr -> MINUS expr"));
                        }
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::MINUS) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::expr(arg1)) =
                            right.pop().unwrap()
                        {
                            let mut arg0 = ();
                            let mut arg1 = arg1;
                            {
                                return NonTerm::expr(-arg1);
                            }
                            return NonTerm::expr(todo!("Implement for rule: expr -> MINUS expr"));
                        }
                    }
                    unreachable!();
                }),
                Token::MULT => parser.shift(14),
                Token::MINUS => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::MINUS) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::expr(arg1)) =
                            right.pop().unwrap()
                        {
                            let mut arg0 = ();
                            let mut arg1 = arg1;
                            {
                                return NonTerm::expr(-arg1);
                            }
                            return NonTerm::expr(todo!("Implement for rule: expr -> MINUS expr"));
                        }
                    }
                    unreachable!();
                }),
                Token::DIV => parser.shift(13),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            20 => match parser.lookahead() {
                Token::LPAREN => parser.shift(7),
                Token::NUM(_) => parser.shift(5),
                Token::IDENT(_) => parser.shift(9),
                Token::MINUS => parser.shift(4),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            21 => match parser.lookahead() {
                Token::MULT => parser.shift(14),
                Token::PLUS => parser.shift(12),
                Token::DIV => parser.shift(13),
                Token::SEMICOLON => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {
                        if let parser::StackElement::Token(Token::ASSIGN) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = arg0;
                                let mut arg1 = ();
                                let mut arg2 = arg2;
                                {
                                    driver.set(arg0, arg2);
                                }
                                return NonTerm::statement;
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MINUS => parser.shift(11),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            22 => match parser.lookahead() {
                Token::NUM(_) => parser.shift(5),
                Token::IDENT(_) => parser.shift(6),
                Token::MINUS => parser.shift(4),
                Token::END => parser.reduce(0, |right| {
                    let mut right = right;

                    return NonTerm::input;
                    unreachable!();
                }),
                Token::LPAREN => parser.shift(7),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            23 => match parser.lookahead() {
                Token::END => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::statement) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::SEMICOLON) = right.pop().unwrap()
                        {
                            if let parser::StackElement::NonTerminal(NonTerm::input) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = ();
                                let mut arg1 = ();
                                let mut arg2 = ();

                                return NonTerm::input;
                            }
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            _ => parser.panic_location(filename, "Unexpected token"),
        }
    }
}
