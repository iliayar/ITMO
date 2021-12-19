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

use super::driver;

#[derive(Debug)]
pub enum Token {
    SEMICOLON,
    IDENT(String),
    DIV,
    PLUS,
    NUM(i64),
    LPAREN,
    END,
    ASSIGN,
    MINUS,
    MULT,
    RPAREN,
}

#[derive(Debug)]
pub enum NonTerm {
    input,
    statement,
    expr(i64),
    S,
}

pub fn parse(input: &str) -> () {
    let mut driver = driver::CalcDriver::new();

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

    let tokens = match lexems.lex(input) {
        Ok(res) => res,
        Err(lex_err) => {
            prety_print_lex_error("stdin", input, lex_err);
            panic!("Failed to lex file");
        }
    };

    let mut parser = parser::Parser::new(tokens, |state, nt| match state {
        0 => match nt {
            NonTerm::statement => Some(2),
            NonTerm::input => Some(1),
            NonTerm::expr(_) => Some(3),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        1 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        2 => match nt {
            NonTerm::statement => Some(2),
            NonTerm::input => Some(24),
            NonTerm::expr(_) => Some(3),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        3 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        4 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        5 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        6 => match nt {
            NonTerm::expr(_) => Some(10),
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
            NonTerm::expr(_) => Some(19),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        12 => match nt {
            NonTerm::expr(_) => Some(18),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        13 => match nt {
            NonTerm::expr(_) => Some(17),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        14 => match nt {
            NonTerm::expr(_) => Some(16),
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
            NonTerm::S => None,
            _ => unreachable!(),
        },

        23 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        24 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        _ => unreachable!(),
    });

    while !parser.accepted() {
        match parser.state() {
            0 => match parser.lookahead() {
                Token::LPAREN => parser.shift(6),
                Token::END => parser.reduce(0, |right| {
                    let mut right = right;

                    return NonTerm::input;
                    unreachable!();
                }),
                Token::MINUS => parser.shift(7),
                Token::NUM(_) => parser.shift(5),
                Token::IDENT(_) => parser.shift(4),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            1 => match parser.lookahead() {
                Token::END => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::input) = right.pop().unwrap()
                    {
                        let mut arg0 = ();

                        return NonTerm::S;
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            2 => match parser.lookahead() {
                Token::LPAREN => parser.shift(6),
                Token::IDENT(_) => parser.shift(4),
                Token::NUM(_) => parser.shift(5),
                Token::END => parser.reduce(0, |right| {
                    let mut right = right;

                    return NonTerm::input;
                    unreachable!();
                }),
                Token::MINUS => parser.shift(7),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            3 => match parser.lookahead() {
                Token::MINUS => parser.shift(13),
                Token::PLUS => parser.shift(12),
                Token::SEMICOLON => parser.shift(23),
                Token::DIV => parser.shift(11),
                Token::MULT => parser.shift(14),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            4 => match parser.lookahead() {
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
                Token::ASSIGN => parser.shift(20),
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

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            5 => match parser.lookahead() {
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

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            6 => match parser.lookahead() {
                Token::IDENT(_) => parser.shift(9),
                Token::NUM(_) => parser.shift(5),
                Token::LPAREN => parser.shift(6),
                Token::MINUS => parser.shift(7),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            7 => match parser.lookahead() {
                Token::LPAREN => parser.shift(6),
                Token::NUM(_) => parser.shift(5),
                Token::MINUS => parser.shift(7),
                Token::IDENT(_) => parser.shift(9),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            8 => match parser.lookahead() {
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
                Token::DIV => parser.reduce(2, |right| {
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
                Token::MULT => parser.reduce(2, |right| {
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

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            9 => match parser.lookahead() {
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

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            10 => match parser.lookahead() {
                Token::PLUS => parser.shift(12),
                Token::MINUS => parser.shift(13),
                Token::MULT => parser.shift(14),
                Token::DIV => parser.shift(11),
                Token::RPAREN => parser.shift(15),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            11 => match parser.lookahead() {
                Token::IDENT(_) => parser.shift(9),
                Token::MINUS => parser.shift(7),
                Token::NUM(_) => parser.shift(5),
                Token::LPAREN => parser.shift(6),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            12 => match parser.lookahead() {
                Token::LPAREN => parser.shift(6),
                Token::NUM(_) => parser.shift(5),
                Token::IDENT(_) => parser.shift(9),
                Token::MINUS => parser.shift(7),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            13 => match parser.lookahead() {
                Token::MINUS => parser.shift(7),
                Token::LPAREN => parser.shift(6),
                Token::IDENT(_) => parser.shift(9),
                Token::NUM(_) => parser.shift(5),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            14 => match parser.lookahead() {
                Token::NUM(_) => parser.shift(5),
                Token::IDENT(_) => parser.shift(9),
                Token::LPAREN => parser.shift(6),
                Token::MINUS => parser.shift(7),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            15 => match parser.lookahead() {
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

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            16 => match parser.lookahead() {
                Token::PLUS => parser.shift(12),
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
                Token::MINUS => parser.shift(13),
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

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            17 => match parser.lookahead() {
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
                Token::DIV => parser.reduce(3, |right| {
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
                Token::MULT => parser.reduce(3, |right| {
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

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            18 => match parser.lookahead() {
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
                Token::MULT => parser.reduce(3, |right| {
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
                Token::DIV => parser.reduce(3, |right| {
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

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            19 => match parser.lookahead() {
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
                Token::PLUS => parser.shift(12),
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
                Token::MINUS => parser.shift(13),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            20 => match parser.lookahead() {
                Token::IDENT(_) => parser.shift(9),
                Token::MINUS => parser.shift(7),
                Token::NUM(_) => parser.shift(5),
                Token::LPAREN => parser.shift(6),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            21 => match parser.lookahead() {
                Token::SEMICOLON => parser.shift(22),
                Token::DIV => parser.shift(11),
                Token::PLUS => parser.shift(12),
                Token::MULT => parser.shift(14),
                Token::MINUS => parser.shift(13),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            22 => match parser.lookahead() {
                Token::END => parser.reduce(4, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {
                        if let parser::StackElement::Token(Token::ASSIGN) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                if let parser::StackElement::Token(Token::SEMICOLON) =
                                    right.pop().unwrap()
                                {
                                    let mut arg0 = arg0;
                                    let mut arg1 = ();
                                    let mut arg2 = arg2;
                                    let mut arg3 = ();
                                    {
                                        driver.set(arg0, arg2);
                                    }
                                    return NonTerm::statement;
                                }
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::LPAREN => parser.reduce(4, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {
                        if let parser::StackElement::Token(Token::ASSIGN) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                if let parser::StackElement::Token(Token::SEMICOLON) =
                                    right.pop().unwrap()
                                {
                                    let mut arg0 = arg0;
                                    let mut arg1 = ();
                                    let mut arg2 = arg2;
                                    let mut arg3 = ();
                                    {
                                        driver.set(arg0, arg2);
                                    }
                                    return NonTerm::statement;
                                }
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MINUS => parser.reduce(4, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {
                        if let parser::StackElement::Token(Token::ASSIGN) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                if let parser::StackElement::Token(Token::SEMICOLON) =
                                    right.pop().unwrap()
                                {
                                    let mut arg0 = arg0;
                                    let mut arg1 = ();
                                    let mut arg2 = arg2;
                                    let mut arg3 = ();
                                    {
                                        driver.set(arg0, arg2);
                                    }
                                    return NonTerm::statement;
                                }
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::IDENT(_) => parser.reduce(4, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {
                        if let parser::StackElement::Token(Token::ASSIGN) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                if let parser::StackElement::Token(Token::SEMICOLON) =
                                    right.pop().unwrap()
                                {
                                    let mut arg0 = arg0;
                                    let mut arg1 = ();
                                    let mut arg2 = arg2;
                                    let mut arg3 = ();
                                    {
                                        driver.set(arg0, arg2);
                                    }
                                    return NonTerm::statement;
                                }
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::NUM(_) => parser.reduce(4, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {
                        if let parser::StackElement::Token(Token::ASSIGN) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::expr(arg2)) =
                                right.pop().unwrap()
                            {
                                if let parser::StackElement::Token(Token::SEMICOLON) =
                                    right.pop().unwrap()
                                {
                                    let mut arg0 = arg0;
                                    let mut arg1 = ();
                                    let mut arg2 = arg2;
                                    let mut arg3 = ();
                                    {
                                        driver.set(arg0, arg2);
                                    }
                                    return NonTerm::statement;
                                }
                            }
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            23 => match parser.lookahead() {
                Token::MINUS => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::SEMICOLON) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = ();
                            {
                                driver.eval(arg0);
                            }
                            return NonTerm::statement;
                        }
                    }
                    unreachable!();
                }),
                Token::LPAREN => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::SEMICOLON) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = ();
                            {
                                driver.eval(arg0);
                            }
                            return NonTerm::statement;
                        }
                    }
                    unreachable!();
                }),
                Token::NUM(_) => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::SEMICOLON) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = ();
                            {
                                driver.eval(arg0);
                            }
                            return NonTerm::statement;
                        }
                    }
                    unreachable!();
                }),
                Token::IDENT(_) => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::SEMICOLON) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = ();
                            {
                                driver.eval(arg0);
                            }
                            return NonTerm::statement;
                        }
                    }
                    unreachable!();
                }),
                Token::END => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::SEMICOLON) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = ();
                            {
                                driver.eval(arg0);
                            }
                            return NonTerm::statement;
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            24 => match parser.lookahead() {
                Token::END => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::statement) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::NonTerminal(NonTerm::input) =
                            right.pop().unwrap()
                        {
                            let mut arg0 = ();
                            let mut arg1 = ();

                            return NonTerm::input;
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            _ => parser.panic_location("<filename>", input, "Unexpected token"),
        }
    }
}
