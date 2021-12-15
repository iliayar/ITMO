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
    PLUS,
    MULT,
    LPAREN,
    RPAREN,
    NUM(usize),
    END,
}

#[derive(Debug)]
pub enum NonTerm {
    E(usize),
    S,
    T(usize),
    F(usize),
}

pub fn parse(input: &str) {
    let mut i = 0usize;

    let mut lexems = lexer::Lexer::new(Token::END);
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

    let mut parser =
        parser::Parser::<Token, NonTerm, Vec<Token>>::new(tokens, |state, nt| match state {
            0 => match nt {
                NonTerm::T(_) => Some(2),
                NonTerm::F(_) => Some(3),
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
                NonTerm::S => None,
                _ => unreachable!(),
            },

            4 => match nt {
                NonTerm::F(_) => Some(3),
                NonTerm::E(_) => Some(8),
                NonTerm::T(_) => Some(2),
                NonTerm::S => None,
                _ => unreachable!(),
            },

            5 => match nt {
                NonTerm::S => None,
                _ => unreachable!(),
            },

            6 => match nt {
                NonTerm::T(_) => Some(9),
                NonTerm::F(_) => Some(3),
                NonTerm::S => None,
                _ => unreachable!(),
            },

            7 => match nt {
                NonTerm::F(_) => Some(10),
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

            _ => unreachable!(),
        });

    while !parser.accepted() {
        parser::print_parser_state(&parser);
        match parser.state() {
            0 => match parser.lookahead() {
                Token::NUM(_) => parser.shift(5),
                Token::LPAREN => parser.shift(4),

                _ => unreachable!(),
            },

            1 => match parser.lookahead() {
                Token::END => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        return NonTerm::S;
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.shift(6),

                _ => unreachable!(),
            },

            2 => match parser.lookahead() {
                Token::RPAREN => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::T(arg0)) =
                        right.pop().unwrap()
                    {
                        return NonTerm::E(arg0);
                    }
                    unreachable!();
                }),
                Token::END => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::T(arg0)) =
                        right.pop().unwrap()
                    {
                        return NonTerm::E(arg0);
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::T(arg0)) =
                        right.pop().unwrap()
                    {
                        return NonTerm::E(arg0);
                    }
                    unreachable!();
                }),
                Token::MULT => parser.shift(7),

                _ => unreachable!(),
            },

            3 => match parser.lookahead() {
                Token::MULT => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::F(arg0)) =
                        right.pop().unwrap()
                    {
                        return NonTerm::T(arg0);
                    }
                    unreachable!();
                }),
                Token::END => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::F(arg0)) =
                        right.pop().unwrap()
                    {
                        return NonTerm::T(arg0);
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::F(arg0)) =
                        right.pop().unwrap()
                    {
                        return NonTerm::T(arg0);
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::F(arg0)) =
                        right.pop().unwrap()
                    {
                        return NonTerm::T(arg0);
                    }
                    unreachable!();
                }),

                _ => unreachable!(),
            },

            4 => match parser.lookahead() {
                Token::LPAREN => parser.shift(4),
                Token::NUM(_) => parser.shift(5),

                _ => unreachable!(),
            },

            5 => match parser.lookahead() {
                Token::PLUS => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::NUM(arg0)) = right.pop().unwrap() {
                        {
                            i += 1;
                            return NonTerm::F(arg0);
                        }
                    }
                    unreachable!();
                }),
                Token::MULT => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::NUM(arg0)) = right.pop().unwrap() {
                        {
                            i += 1;
                            return NonTerm::F(arg0);
                        }
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::NUM(arg0)) = right.pop().unwrap() {
                        {
                            i += 1;
                            return NonTerm::F(arg0);
                        }
                    }
                    unreachable!();
                }),
                Token::END => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::NUM(arg0)) = right.pop().unwrap() {
                        {
                            i += 1;
                            return NonTerm::F(arg0);
                        }
                    }
                    unreachable!();
                }),

                _ => unreachable!(),
            },

            6 => match parser.lookahead() {
                Token::LPAREN => parser.shift(4),
                Token::NUM(_) => parser.shift(5),

                _ => unreachable!(),
            },

            7 => match parser.lookahead() {
                Token::LPAREN => parser.shift(4),
                Token::NUM(_) => parser.shift(5),

                _ => unreachable!(),
            },

            8 => match parser.lookahead() {
                Token::RPAREN => parser.shift(11),
                Token::PLUS => parser.shift(6),

                _ => unreachable!(),
            },

            9 => match parser.lookahead() {
                Token::PLUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::PLUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::T(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 + arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MULT => parser.shift(7),
                Token::RPAREN => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::E(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::PLUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::T(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 + arg2);
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
                        if let parser::StackElement::Token(Token::PLUS) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::T(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::E(arg0 + arg2);
                            }
                        }
                    }
                    unreachable!();
                }),

                _ => unreachable!(),
            },

            10 => match parser.lookahead() {
                Token::MULT => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::T(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MULT) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::F(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::T(arg0 * arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::T(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MULT) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::F(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::T(arg0 * arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::T(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MULT) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::F(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::T(arg0 * arg2);
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::END => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::T(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::MULT) = right.pop().unwrap() {
                            if let parser::StackElement::NonTerminal(NonTerm::F(arg2)) =
                                right.pop().unwrap()
                            {
                                return NonTerm::T(arg0 * arg2);
                            }
                        }
                    }
                    unreachable!();
                }),

                _ => unreachable!(),
            },

            11 => match parser.lookahead() {
                Token::END => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LPAREN) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::E(arg1)) =
                            right.pop().unwrap()
                        {
                            if let parser::StackElement::Token(Token::RPAREN) = right.pop().unwrap()
                            {
                                {
                                    i += 0;
                                    return NonTerm::F(arg1);
                                }
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MULT => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LPAREN) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::E(arg1)) =
                            right.pop().unwrap()
                        {
                            if let parser::StackElement::Token(Token::RPAREN) = right.pop().unwrap()
                            {
                                {
                                    i += 0;
                                    return NonTerm::F(arg1);
                                }
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
                                {
                                    i += 0;
                                    return NonTerm::F(arg1);
                                }
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
                                {
                                    i += 0;
                                    return NonTerm::F(arg1);
                                }
                            }
                        }
                    }
                    unreachable!();
                }),

                _ => unreachable!(),
            },

            _ => panic!("Ooops..."),
        }
    }

    println!("i: {}", i);
}
