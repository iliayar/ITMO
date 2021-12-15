#![allow(non_snake_case, unused_variables, dead_code, unreachable_patterns)]
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
    F,
    T,
    E,
    S,
}

pub fn parse(input: &str) {
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

    println!("{:?}", tokens);

    let mut parser =
        parser::Parser::<Token, NonTerm, Vec<Token>>::new(tokens, |state, nt| match state {
            0 => match nt {
                NonTerm::T => Some(2),
                NonTerm::E => Some(3),
                NonTerm::F => Some(1),
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
                NonTerm::E => Some(8),
                NonTerm::F => Some(1),
                NonTerm::T => Some(2),
                NonTerm::S => None,
                _ => unreachable!(),
            },

            5 => match nt {
                NonTerm::S => None,
                _ => unreachable!(),
            },

            6 => match nt {
                NonTerm::F => Some(9),
                NonTerm::S => None,
                _ => unreachable!(),
            },

            7 => match nt {
                NonTerm::F => Some(1),
                NonTerm::T => Some(10),
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
                Token::PLUS => parser.reduce(1, |right| {
                    if let parser::StackElement::NonTerminal(NonTerm::F) = right[0] {
                        return NonTerm::T;
                    }
                    unreachable!();
                }),
                Token::END => parser.reduce(1, |right| {
                    if let parser::StackElement::NonTerminal(NonTerm::F) = right[0] {
                        return NonTerm::T;
                    }
                    unreachable!();
                }),
                Token::MULT => parser.reduce(1, |right| {
                    if let parser::StackElement::NonTerminal(NonTerm::F) = right[0] {
                        return NonTerm::T;
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(1, |right| {
                    if let parser::StackElement::NonTerminal(NonTerm::F) = right[0] {
                        return NonTerm::T;
                    }
                    unreachable!();
                }),

                _ => unreachable!(),
            },

            2 => match parser.lookahead() {
                Token::MULT => parser.shift(6),
                Token::PLUS => parser.reduce(1, |right| {
                    if let parser::StackElement::NonTerminal(NonTerm::T) = right[0] {
                        return NonTerm::E;
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(1, |right| {
                    if let parser::StackElement::NonTerminal(NonTerm::T) = right[0] {
                        return NonTerm::E;
                    }
                    unreachable!();
                }),
                Token::END => parser.reduce(1, |right| {
                    if let parser::StackElement::NonTerminal(NonTerm::T) = right[0] {
                        return NonTerm::E;
                    }
                    unreachable!();
                }),

                _ => unreachable!(),
            },

            3 => match parser.lookahead() {
                Token::PLUS => parser.shift(7),
                Token::END => parser.reduce(1, |right| {
                    if let parser::StackElement::NonTerminal(NonTerm::E) = right[0] {
                        return NonTerm::S;
                    }
                    unreachable!();
                }),

                _ => unreachable!(),
            },

            4 => match parser.lookahead() {
                Token::NUM(_) => parser.shift(5),
                Token::LPAREN => parser.shift(4),

                _ => unreachable!(),
            },

            5 => match parser.lookahead() {
                Token::MULT => parser.reduce(1, |right| {
                    if let parser::StackElement::Token(Token::NUM(arg0)) = right[0] {
                        return NonTerm::F;
                    }
                    unreachable!();
                }),
                Token::END => parser.reduce(1, |right| {
                    if let parser::StackElement::Token(Token::NUM(arg0)) = right[0] {
                        return NonTerm::F;
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(1, |right| {
                    if let parser::StackElement::Token(Token::NUM(arg0)) = right[0] {
                        return NonTerm::F;
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(1, |right| {
                    if let parser::StackElement::Token(Token::NUM(arg0)) = right[0] {
                        return NonTerm::F;
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
                Token::PLUS => parser.shift(7),

                _ => unreachable!(),
            },

            9 => match parser.lookahead() {
                Token::RPAREN => parser.reduce(3, |right| {
                    if let parser::StackElement::NonTerminal(NonTerm::T) = right[0] {
                        if let parser::StackElement::Token(Token::MULT) = right[1] {
                            if let parser::StackElement::NonTerminal(NonTerm::F) = right[2] {
                                return NonTerm::T;
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MULT => parser.reduce(3, |right| {
                    if let parser::StackElement::NonTerminal(NonTerm::T) = right[0] {
                        if let parser::StackElement::Token(Token::MULT) = right[1] {
                            if let parser::StackElement::NonTerminal(NonTerm::F) = right[2] {
                                return NonTerm::T;
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::END => parser.reduce(3, |right| {
                    if let parser::StackElement::NonTerminal(NonTerm::T) = right[0] {
                        if let parser::StackElement::Token(Token::MULT) = right[1] {
                            if let parser::StackElement::NonTerminal(NonTerm::F) = right[2] {
                                return NonTerm::T;
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(3, |right| {
                    if let parser::StackElement::NonTerminal(NonTerm::T) = right[0] {
                        if let parser::StackElement::Token(Token::MULT) = right[1] {
                            if let parser::StackElement::NonTerminal(NonTerm::F) = right[2] {
                                return NonTerm::T;
                            }
                        }
                    }
                    unreachable!();
                }),

                _ => unreachable!(),
            },

            10 => match parser.lookahead() {
                Token::RPAREN => parser.reduce(3, |right| {
                    if let parser::StackElement::NonTerminal(NonTerm::E) = right[0] {
                        if let parser::StackElement::Token(Token::PLUS) = right[1] {
                            if let parser::StackElement::NonTerminal(NonTerm::T) = right[2] {
                                return NonTerm::E;
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MULT => parser.shift(6),
                Token::PLUS => parser.reduce(3, |right| {
                    if let parser::StackElement::NonTerminal(NonTerm::E) = right[0] {
                        if let parser::StackElement::Token(Token::PLUS) = right[1] {
                            if let parser::StackElement::NonTerminal(NonTerm::T) = right[2] {
                                return NonTerm::E;
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::END => parser.reduce(3, |right| {
                    if let parser::StackElement::NonTerminal(NonTerm::E) = right[0] {
                        if let parser::StackElement::Token(Token::PLUS) = right[1] {
                            if let parser::StackElement::NonTerminal(NonTerm::T) = right[2] {
                                return NonTerm::E;
                            }
                        }
                    }
                    unreachable!();
                }),

                _ => unreachable!(),
            },

            11 => match parser.lookahead() {
                Token::END => parser.reduce(3, |right| {
                    if let parser::StackElement::Token(Token::LPAREN) = right[0] {
                        if let parser::StackElement::NonTerminal(NonTerm::E) = right[1] {
                            if let parser::StackElement::Token(Token::RPAREN) = right[2] {
                                return NonTerm::F;
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(3, |right| {
                    if let parser::StackElement::Token(Token::LPAREN) = right[0] {
                        if let parser::StackElement::NonTerminal(NonTerm::E) = right[1] {
                            if let parser::StackElement::Token(Token::RPAREN) = right[2] {
                                return NonTerm::F;
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(3, |right| {
                    if let parser::StackElement::Token(Token::LPAREN) = right[0] {
                        if let parser::StackElement::NonTerminal(NonTerm::E) = right[1] {
                            if let parser::StackElement::Token(Token::RPAREN) = right[2] {
                                return NonTerm::F;
                            }
                        }
                    }
                    unreachable!();
                }),
                Token::MULT => parser.reduce(3, |right| {
                    if let parser::StackElement::Token(Token::LPAREN) = right[0] {
                        if let parser::StackElement::NonTerminal(NonTerm::E) = right[1] {
                            if let parser::StackElement::Token(Token::RPAREN) = right[2] {
                                return NonTerm::F;
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
}
