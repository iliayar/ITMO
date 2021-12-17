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

use super::driver;

#[derive(Debug)]
pub enum Token {
    SECTION_SPLIT,
    END,
    LITERAL(String),
    PROP(String),
    CODE(String),
}

#[derive(Debug)]
pub enum NonTerm {
    TERMS,
    PROP,
    SECTION2,
    SECTION1,
    SECTION3,
    PROPS,
    DOC,
    S,
    TERM,
}

pub fn parse(input: &str) -> driver::lexer::Lex {
    let mut builder = driver::lexer::LexBuilder::new();

    let mut lexems = lexer::Lexer::new(Token::END);
    lexems.add("\"\\s\"", |s| {
        println!("Whitespace!");
        None
    });
    lexems.add("\"%%\\n\"", |s| Some(Token::SECTION_SPLIT));
    lexems.add("\"\\\"([^\\\"\\\\]|\\\\[\\s\\S])*\\\"\"", |s| {
        Some(Token::LITERAL(s))
    });
    lexems.add("\"\\{([^\\{\\}\\\\]|\\\\[\\s\\S])*(\\{([^\\{\\}\\\\]|\\\\[\\s\\S])*\\}|([^\\{\\}\\\\]|\\\\[\\s\\S])*)*\\}\"", |s| { Some(Token::CODE(s)) });
    lexems.add("\"%[a-zA-Z0_-]+\"", |s| Some(Token::PROP(s)));

    let tokens = match lexems.lex(input) {
        Ok(res) => res,
        Err(lex_err) => {
            prety_print_lex_error("stdin", input, lex_err);
            panic!("Failed to lex file");
        }
    };

    let mut parser = parser::Parser::new(tokens, |state, nt| match state {
        0 => match nt {
            NonTerm::DOC => Some(4),
            NonTerm::PROP => Some(1),
            NonTerm::SECTION1 => Some(2),
            NonTerm::PROPS => Some(3),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        1 => match nt {
            NonTerm::PROPS => Some(16),
            NonTerm::PROP => Some(1),
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
            NonTerm::TERMS => Some(8),
            NonTerm::SECTION2 => Some(9),
            NonTerm::TERM => Some(10),
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
            NonTerm::TERM => Some(10),
            NonTerm::TERMS => Some(13),
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

        14 => match nt {
            NonTerm::SECTION3 => Some(15),
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
        parser::print_parser_state(&parser);
        match parser.state() {
            0 => match parser.lookahead() {
                Token::SECTION_SPLIT => parser.reduce(0, |right| {
                    let mut right = right;

                    return NonTerm::PROPS;
                    unreachable!();
                }),
                Token::PROP(_) => parser.shift(5),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            1 => match parser.lookahead() {
                Token::PROP(_) => parser.shift(5),
                Token::SECTION_SPLIT => parser.reduce(0, |right| {
                    let mut right = right;

                    return NonTerm::PROPS;
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            2 => match parser.lookahead() {
                Token::SECTION_SPLIT => parser.shift(7),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            3 => match parser.lookahead() {
                Token::SECTION_SPLIT => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::PROPS) = right.pop().unwrap()
                    {
                        let mut arg0 = ();

                        return NonTerm::SECTION1;
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            4 => match parser.lookahead() {
                Token::END => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::DOC) = right.pop().unwrap() {
                        let mut arg0 = ();

                        return NonTerm::S;
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            5 => match parser.lookahead() {
                Token::LITERAL(_) => parser.shift(6),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            6 => match parser.lookahead() {
                Token::SECTION_SPLIT => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::PROP(arg0)) = right.pop().unwrap() {
                        if let parser::StackElement::Token(Token::LITERAL(arg1)) =
                            right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = arg1;

                            {
                                match arg0.as_ref() {
                                    "%end" => {
                                        builder.end(arg1.trim_matches('"').to_string());
                                    }
                                    _ => {
                                        panic!("Invalid property: {}", arg0);
                                    }
                                }
                            }

                            return NonTerm::PROP;
                        }
                    }
                    unreachable!();
                }),
                Token::PROP(_) => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::PROP(arg0)) = right.pop().unwrap() {
                        if let parser::StackElement::Token(Token::LITERAL(arg1)) =
                            right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = arg1;

                            {
                                match arg0.as_ref() {
                                    "%end" => {
                                        builder.end(arg1.trim_matches('"').to_string());
                                    }
                                    _ => {
                                        panic!("Invalid property: {}", arg0);
                                    }
                                }
                            }

                            return NonTerm::PROP;
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            7 => match parser.lookahead() {
                Token::SECTION_SPLIT => parser.reduce(0, |right| {
                    let mut right = right;

                    return NonTerm::TERMS;
                    unreachable!();
                }),
                Token::LITERAL(_) => parser.shift(11),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            8 => match parser.lookahead() {
                Token::SECTION_SPLIT => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::TERMS) = right.pop().unwrap()
                    {
                        let mut arg0 = ();

                        return NonTerm::SECTION2;
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            9 => match parser.lookahead() {
                Token::SECTION_SPLIT => parser.shift(14),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            10 => match parser.lookahead() {
                Token::LITERAL(_) => parser.shift(11),
                Token::SECTION_SPLIT => parser.reduce(0, |right| {
                    let mut right = right;

                    return NonTerm::TERMS;
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            11 => match parser.lookahead() {
                Token::CODE(_) => parser.shift(12),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            12 => match parser.lookahead() {
                Token::LITERAL(_) => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LITERAL(arg0)) = right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::CODE(arg1)) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = arg1;

                            {
                                builder.add_token(driver::lexer::Token::new(arg0, arg1));
                            }

                            return NonTerm::TERM;
                        }
                    }
                    unreachable!();
                }),
                Token::SECTION_SPLIT => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LITERAL(arg0)) = right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::CODE(arg1)) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = arg1;

                            {
                                builder.add_token(driver::lexer::Token::new(arg0, arg1));
                            }

                            return NonTerm::TERM;
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            13 => match parser.lookahead() {
                Token::SECTION_SPLIT => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::TERM) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::TERMS) =
                            right.pop().unwrap()
                        {
                            let mut arg0 = ();
                            let mut arg1 = ();

                            return NonTerm::TERMS;
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            14 => match parser.lookahead() {
                Token::END => parser.reduce(0, |right| {
                    let mut right = right;

                    return NonTerm::SECTION3;
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            15 => match parser.lookahead() {
                Token::END => parser.reduce(5, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::SECTION1) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::SECTION_SPLIT) =
                            right.pop().unwrap()
                        {
                            if let parser::StackElement::NonTerminal(NonTerm::SECTION2) =
                                right.pop().unwrap()
                            {
                                if let parser::StackElement::Token(Token::SECTION_SPLIT) =
                                    right.pop().unwrap()
                                {
                                    if let parser::StackElement::NonTerminal(NonTerm::SECTION3) =
                                        right.pop().unwrap()
                                    {
                                        let mut arg0 = ();
                                        let mut arg1 = ();
                                        let mut arg2 = ();
                                        let mut arg3 = ();
                                        let mut arg4 = ();

                                        return NonTerm::DOC;
                                    }
                                }
                            }
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            16 => match parser.lookahead() {
                Token::SECTION_SPLIT => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::PROP) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::PROPS) =
                            right.pop().unwrap()
                        {
                            let mut arg0 = ();
                            let mut arg1 = ();

                            return NonTerm::PROPS;
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            _ => parser.panic_location("<filename>", input, "Unexpected token"),
        }
    }

    return builder.build();
}
