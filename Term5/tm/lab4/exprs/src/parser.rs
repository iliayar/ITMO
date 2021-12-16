#![allow(
    non_snake_case,
    unused_variables,
    dead_code,
    unreachable_patterns,
    unreachable_code
)]
use parslib::*;

#[derive(Debug)]
pub enum Token {
    MULT,
    PLUS,
    MINUS,
    DIV,
    LPAREN,
    RPAREN,
    NUM(i64),
    END,
}

#[derive(Debug)]
pub enum NonTerm {
    E(i64),
    S,
}

pub fn parse(input: &str) {
    let mut lexems = lexer::Lexer::new(Token::END);
    lexems.add(r"\+", |s| Some(Token::PLUS));
    lexems.add(r"\*", |s| Some(Token::MULT));
    lexems.add(r"-", |s| Some(Token::MINUS));
    lexems.add(r"/", |s| Some(Token::DIV));
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

    let mut parser = parser::Parser::new(tokens, |state, nt| match state {
        0 => match nt {
            NonTerm::E(_) => Some(1),
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
            NonTerm::E(_) => Some(8),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        4 => match nt {
            NonTerm::E(_) => Some(9),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        5 => match nt {
            NonTerm::E(_) => Some(10),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        6 => match nt {
            NonTerm::E(_) => Some(11),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        7 => match nt {
            NonTerm::E(_) => Some(12),
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

        _ => unreachable!(),
    });

    while !parser.accepted() {
        parser::print_parser_state(&parser);
        match parser.state() {
            0 => match parser.lookahead() {
                Token::LPAREN => parser.shift(3),
                Token::NUM(_) => parser.shift(2),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            1 => match parser.lookahead() {
                Token::PLUS => parser.shift(6),
                Token::MULT => parser.shift(5),
                Token::DIV => parser.shift(7),
                Token::MINUS => parser.shift(4),
                Token::END => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        return NonTerm::S;
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            2 => match parser.lookahead() {
                Token::END => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::NUM(arg0)) = right.pop().unwrap() {
                        return NonTerm::E(arg0);
                    }
                    unreachable!();
                }),
                Token::MINUS => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::NUM(arg0)) = right.pop().unwrap() {
                        return NonTerm::E(arg0);
                    }
                    unreachable!();
                }),
                Token::MULT => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::NUM(arg0)) = right.pop().unwrap() {
                        return NonTerm::E(arg0);
                    }
                    unreachable!();
                }),
                Token::DIV => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::NUM(arg0)) = right.pop().unwrap() {
                        return NonTerm::E(arg0);
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::NUM(arg0)) = right.pop().unwrap() {
                        return NonTerm::E(arg0);
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::NUM(arg0)) = right.pop().unwrap() {
                        return NonTerm::E(arg0);
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            3 => match parser.lookahead() {
                Token::NUM(_) => parser.shift(2),
                Token::LPAREN => parser.shift(3),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            4 => match parser.lookahead() {
                Token::NUM(_) => parser.shift(2),
                Token::LPAREN => parser.shift(3),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            5 => match parser.lookahead() {
                Token::LPAREN => parser.shift(3),
                Token::NUM(_) => parser.shift(2),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            6 => match parser.lookahead() {
                Token::NUM(_) => parser.shift(2),
                Token::LPAREN => parser.shift(3),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            7 => match parser.lookahead() {
                Token::NUM(_) => parser.shift(2),
                Token::LPAREN => parser.shift(3),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            8 => match parser.lookahead() {
                Token::MULT => parser.shift(5),
                Token::RPAREN => parser.shift(13),
                Token::PLUS => parser.shift(6),
                Token::DIV => parser.shift(7),
                Token::MINUS => parser.shift(4),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            9 => match parser.lookahead() {
                Token::DIV => parser.shift(7),
                Token::END => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MINUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 - arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MINUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 - arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MULT => parser.shift(5),
                Token::MINUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MINUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 - arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MINUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 - arg2);
                            }
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            10 => match parser.lookahead() {
                Token::PLUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MULT) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 * arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MINUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MULT) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 * arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::DIV => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MULT) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 * arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::END => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MULT) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 * arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MULT) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 * arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MULT => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MULT) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 * arg2);
                            }
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            11 => match parser.lookahead() {
                Token::PLUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::PLUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 + arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::DIV => parser.shift(7),
                Token::RPAREN => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::PLUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 + arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MINUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::PLUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 + arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MULT => parser.shift(5),
                Token::END => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::PLUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 + arg2);
                            }
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            12 => match parser.lookahead() {
                Token::MULT => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::DIV) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 / arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::END => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::DIV) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 / arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MINUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::DIV) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 / arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::DIV) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 / arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::DIV) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 / arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::DIV => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::DIV) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::E(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 / arg2);
                            }
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            13 => match parser.lookahead() {
                Token::MULT => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LPAREN) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::E(arg1)) =
                            right.pop().unwrap()
                        {
                            if let parser::StackElement::Token(Token::RPAREN) = right.pop().unwrap()
                            {
                                return NonTerm::E(arg1);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::END => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LPAREN) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::E(arg1)) =
                            right.pop().unwrap()
                        {
                            if let parser::StackElement::Token(Token::RPAREN) = right.pop().unwrap()
                            {
                                return NonTerm::E(arg1);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::DIV => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LPAREN) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::E(arg1)) =
                            right.pop().unwrap()
                        {
                            if let parser::StackElement::Token(Token::RPAREN) = right.pop().unwrap()
                            {
                                return NonTerm::E(arg1);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MINUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LPAREN) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::E(arg1)) =
                            right.pop().unwrap()
                        {
                            if let parser::StackElement::Token(Token::RPAREN) = right.pop().unwrap()
                            {
                                return NonTerm::E(arg1);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LPAREN) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::E(arg1)) =
                            right.pop().unwrap()
                        {
                            if let parser::StackElement::Token(Token::RPAREN) = right.pop().unwrap()
                            {
                                return NonTerm::E(arg1);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LPAREN) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::E(arg1)) =
                            right.pop().unwrap()
                        {
                            if let parser::StackElement::Token(Token::RPAREN) = right.pop().unwrap()
                            {
                                return NonTerm::E(arg1);
                            }
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
