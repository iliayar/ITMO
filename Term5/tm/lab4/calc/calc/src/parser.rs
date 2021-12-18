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

#[derive(Debug)]
pub enum Token {
    PLUS,
    RPAREN,
    END,
    MINUS,
    LPAREN,
    DIV,
    NUM(i64),
    MULT,
}

#[derive(Debug)]
pub enum NonTerm {
    inp,
    S,
    expr(i64),
}

pub fn parse(input: &str) -> i64 {
    let mut res = 0i64;

    let mut lexems = lexer::Lexer::new(Token::END);
    lexems.add("\\s", |s| None);
    lexems.add("[0-9]+", |s| Some(Token::NUM(s.parse().unwrap())));
    lexems.add("\\+", |s| Some(Token::PLUS));
    lexems.add("-", |s| Some(Token::MINUS));
    lexems.add("\\*", |s| Some(Token::MULT));
    lexems.add("/", |s| Some(Token::DIV));
    lexems.add("\\(", |s| Some(Token::LPAREN));
    lexems.add("\\)", |s| Some(Token::RPAREN));

    let tokens = match lexems.lex(input) {
        Ok(res) => res,
        Err(lex_err) => {
            prety_print_lex_error("stdin", input, lex_err);
            panic!("Failed to lex file");
        }
    };

    let mut parser = parser::Parser::new(tokens, |state, nt| match state {
        0 => match nt {
            NonTerm::expr(_) => Some(2),
            NonTerm::inp => Some(1),
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
            NonTerm::expr(_) => Some(16),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        4 => match nt {
            NonTerm::expr(_) => Some(6),
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
            NonTerm::expr(_) => Some(15),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        8 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        9 => match nt {
            NonTerm::expr(_) => Some(14),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        10 => match nt {
            NonTerm::expr(_) => Some(13),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        11 => match nt {
            NonTerm::expr(_) => Some(12),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        12 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        13 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        14 => match nt {
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

        _ => unreachable!(),
    });

    while !parser.accepted() {
        match parser.state() {
            0 => match parser.lookahead() {
                Token::LPAREN => parser.shift(4),
                Token::MINUS => parser.shift(3),
                Token::NUM(_) => parser.shift(5),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            1 => match parser.lookahead() {
                Token::END => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::inp) = right.pop().unwrap() {
                        let mut arg0 = ();

                        return NonTerm::S;
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            2 => match parser.lookahead() {
                Token::DIV => parser.shift(10),
                Token::PLUS => parser.shift(7),
                Token::END => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        let mut arg0 = arg0;
                        {
                            res = arg0;
                        }
                        return NonTerm::inp;
                    }
                    unreachable!();
                }),
                Token::MULT => parser.shift(11),
                Token::MINUS => parser.shift(9),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            3 => match parser.lookahead() {
                Token::LPAREN => parser.shift(4),
                Token::MINUS => parser.shift(3),
                Token::NUM(_) => parser.shift(5),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            4 => match parser.lookahead() {
                Token::MINUS => parser.shift(3),
                Token::LPAREN => parser.shift(4),
                Token::NUM(_) => parser.shift(5),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            5 => match parser.lookahead() {
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
                Token::END => parser.reduce(1, |right| {
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

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            6 => match parser.lookahead() {
                Token::PLUS => parser.shift(7),
                Token::MINUS => parser.shift(9),
                Token::RPAREN => parser.shift(8),
                Token::DIV => parser.shift(10),
                Token::MULT => parser.shift(11),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            7 => match parser.lookahead() {
                Token::LPAREN => parser.shift(4),
                Token::MINUS => parser.shift(3),
                Token::NUM(_) => parser.shift(5),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            8 => match parser.lookahead() {
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
                Token::END => parser.reduce(3, |right| {
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

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            9 => match parser.lookahead() {
                Token::LPAREN => parser.shift(4),
                Token::NUM(_) => parser.shift(5),
                Token::MINUS => parser.shift(3),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            10 => match parser.lookahead() {
                Token::NUM(_) => parser.shift(5),
                Token::MINUS => parser.shift(3),
                Token::LPAREN => parser.shift(4),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            11 => match parser.lookahead() {
                Token::MINUS => parser.shift(3),
                Token::LPAREN => parser.shift(4),
                Token::NUM(_) => parser.shift(5),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            12 => match parser.lookahead() {
                Token::END => parser.reduce(3, |right| {
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
                Token::PLUS => parser.shift(7),
                Token::MINUS => parser.shift(9),
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

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            13 => match parser.lookahead() {
                Token::PLUS => parser.shift(7),
                Token::END => parser.reduce(3, |right| {
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
                Token::MINUS => parser.shift(9),
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

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            14 => match parser.lookahead() {
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
                Token::END => parser.reduce(3, |right| {
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

            15 => match parser.lookahead() {
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
                Token::END => parser.reduce(3, |right| {
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

            16 => match parser.lookahead() {
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
                Token::END => parser.reduce(2, |right| {
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

            _ => parser.panic_location("<filename>", input, "Unexpected token"),
        }
    }

    return res;
}
