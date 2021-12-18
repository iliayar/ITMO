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
    PROP(String),
    END,
    SECTION_SPLIT,
    KEYWORD(String),
    LITERAL(String),
    REGEX(String),
    CODE(String),
}

#[derive(Debug)]
pub enum NonTerm {
    prop,
    third_section,
    terms,
    S,
    doc,
    term,
    props,
    first_section,
    second_section,
}

pub fn parse(input: &str) -> driver::lexer::Lex {
    let mut builder = driver::lexer::LexBuilder::new();

    let mut lexems = lexer::Lexer::new(Token::END);
    lexems.add("\\s", |s| None);
    lexems.add("%%\\n", |s| Some(Token::SECTION_SPLIT));
    lexems.add("\"([^\"\\\\]|\\\\[\\s\\S])*\"", |s| Some(Token::LITERAL(s)));
    lexems.add("'([^'\\\\]|\\\\[\\s\\S])*'", |s| Some(Token::KEYWORD(s)));
    lexems.add("/([^/\\\\]|\\\\[\\s\\S])*/", |s| {
        Some(Token::REGEX(s[1..s.len() - 1].to_string()))
    });
    lexems.add("\\{\\{(?:(?!\\}\\})(.|\\n))+\\}\\}", |s| {
        Some(Token::CODE(s[1..s.len() - 1].to_string()))
    });
    lexems.add("%[a-zA-Z0_-]+", |s| Some(Token::PROP(s)));

    let tokens = match lexems.lex(input) {
        Ok(res) => res,
        Err(lex_err) => {
            prety_print_lex_error("stdin", input, lex_err);
            panic!("Failed to lex file");
        }
    };

    let mut parser = parser::Parser::new(tokens, |state, nt| match state {
        0 => match nt {
            NonTerm::props => Some(3),
            NonTerm::doc => Some(2),
            NonTerm::prop => Some(1),
            NonTerm::first_section => Some(4),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        1 => match nt {
            NonTerm::props => Some(20),
            NonTerm::prop => Some(1),
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
            NonTerm::terms => Some(8),
            NonTerm::second_section => Some(10),
            NonTerm::term => Some(9),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        8 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        9 => match nt {
            NonTerm::term => Some(9),
            NonTerm::terms => Some(19),
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

        17 => match nt {
            NonTerm::third_section => Some(18),
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
            NonTerm::S => None,
            _ => unreachable!(),
        },

        _ => unreachable!(),
    });

    while !parser.accepted() {
        match parser.state() {
            0 => match parser.lookahead() {
                Token::PROP(_) => parser.shift(5),
                Token::SECTION_SPLIT => parser.reduce(0, |right| {
                    let mut right = right;

                    return NonTerm::props;
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            1 => match parser.lookahead() {
                Token::PROP(_) => parser.shift(5),
                Token::SECTION_SPLIT => parser.reduce(0, |right| {
                    let mut right = right;

                    return NonTerm::props;
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            2 => match parser.lookahead() {
                Token::END => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::doc) = right.pop().unwrap() {
                        let mut arg0 = ();

                        return NonTerm::S;
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            3 => match parser.lookahead() {
                Token::SECTION_SPLIT => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::props) = right.pop().unwrap()
                    {
                        let mut arg0 = ();

                        return NonTerm::first_section;
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            4 => match parser.lookahead() {
                Token::SECTION_SPLIT => parser.shift(7),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            5 => match parser.lookahead() {
                Token::LITERAL(_) => parser.shift(6),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            6 => match parser.lookahead() {
                Token::PROP(_) => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::PROP(arg0)) = right.pop().unwrap() {
                        if let parser::StackElement::Token(Token::LITERAL(arg1)) =
                            right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = arg1;
                            {
                                builder.prop(arg0, arg1);
                            }
                            return NonTerm::prop;
                        }
                    }
                    unreachable!();
                }),
                Token::SECTION_SPLIT => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::PROP(arg0)) = right.pop().unwrap() {
                        if let parser::StackElement::Token(Token::LITERAL(arg1)) =
                            right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = arg1;
                            {
                                builder.prop(arg0, arg1);
                            }
                            return NonTerm::prop;
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            7 => match parser.lookahead() {
                Token::KEYWORD(_) => parser.shift(11),
                Token::REGEX(_) => parser.shift(13),
                Token::SECTION_SPLIT => parser.reduce(0, |right| {
                    let mut right = right;

                    return NonTerm::terms;
                    unreachable!();
                }),
                Token::LITERAL(_) => parser.shift(12),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            8 => match parser.lookahead() {
                Token::SECTION_SPLIT => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::terms) = right.pop().unwrap()
                    {
                        let mut arg0 = ();

                        return NonTerm::second_section;
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            9 => match parser.lookahead() {
                Token::LITERAL(_) => parser.shift(12),
                Token::SECTION_SPLIT => parser.reduce(0, |right| {
                    let mut right = right;

                    return NonTerm::terms;
                    unreachable!();
                }),
                Token::REGEX(_) => parser.shift(13),
                Token::KEYWORD(_) => parser.shift(11),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            10 => match parser.lookahead() {
                Token::SECTION_SPLIT => parser.shift(17),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            11 => match parser.lookahead() {
                Token::CODE(_) => parser.shift(16),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            12 => match parser.lookahead() {
                Token::CODE(_) => parser.shift(15),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            13 => match parser.lookahead() {
                Token::CODE(_) => parser.shift(14),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            14 => match parser.lookahead() {
                Token::LITERAL(_) => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::REGEX(arg0)) = right.pop().unwrap() {
                        if let parser::StackElement::Token(Token::CODE(arg1)) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = arg1;
                            {
                                builder.add_token_regex(arg0, arg1);
                            }
                            return NonTerm::term;
                        }
                    }
                    unreachable!();
                }),
                Token::REGEX(_) => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::REGEX(arg0)) = right.pop().unwrap() {
                        if let parser::StackElement::Token(Token::CODE(arg1)) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = arg1;
                            {
                                builder.add_token_regex(arg0, arg1);
                            }
                            return NonTerm::term;
                        }
                    }
                    unreachable!();
                }),
                Token::KEYWORD(_) => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::REGEX(arg0)) = right.pop().unwrap() {
                        if let parser::StackElement::Token(Token::CODE(arg1)) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = arg1;
                            {
                                builder.add_token_regex(arg0, arg1);
                            }
                            return NonTerm::term;
                        }
                    }
                    unreachable!();
                }),
                Token::SECTION_SPLIT => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::REGEX(arg0)) = right.pop().unwrap() {
                        if let parser::StackElement::Token(Token::CODE(arg1)) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = arg1;
                            {
                                builder.add_token_regex(arg0, arg1);
                            }
                            return NonTerm::term;
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            15 => match parser.lookahead() {
                Token::KEYWORD(_) => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LITERAL(arg0)) = right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::CODE(arg1)) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = arg1;
                            {
                                builder.add_token(arg0, arg1);
                            }
                            return NonTerm::term;
                        }
                    }
                    unreachable!();
                }),
                Token::LITERAL(_) => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LITERAL(arg0)) = right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::CODE(arg1)) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = arg1;
                            {
                                builder.add_token(arg0, arg1);
                            }
                            return NonTerm::term;
                        }
                    }
                    unreachable!();
                }),
                Token::REGEX(_) => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::LITERAL(arg0)) = right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::CODE(arg1)) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = arg1;
                            {
                                builder.add_token(arg0, arg1);
                            }
                            return NonTerm::term;
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
                                builder.add_token(arg0, arg1);
                            }
                            return NonTerm::term;
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            16 => match parser.lookahead() {
                Token::SECTION_SPLIT => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::KEYWORD(arg0)) = right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::CODE(arg1)) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = arg1;
                            {
                                builder.add_token_keyword(arg0, arg1);
                            }
                            return NonTerm::term;
                        }
                    }
                    unreachable!();
                }),
                Token::KEYWORD(_) => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::KEYWORD(arg0)) = right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::CODE(arg1)) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = arg1;
                            {
                                builder.add_token_keyword(arg0, arg1);
                            }
                            return NonTerm::term;
                        }
                    }
                    unreachable!();
                }),
                Token::LITERAL(_) => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::KEYWORD(arg0)) = right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::CODE(arg1)) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = arg1;
                            {
                                builder.add_token_keyword(arg0, arg1);
                            }
                            return NonTerm::term;
                        }
                    }
                    unreachable!();
                }),
                Token::REGEX(_) => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::Token(Token::KEYWORD(arg0)) = right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::CODE(arg1)) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = arg1;
                            {
                                builder.add_token_keyword(arg0, arg1);
                            }
                            return NonTerm::term;
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            17 => match parser.lookahead() {
                Token::END => parser.reduce(0, |right| {
                    let mut right = right;

                    return NonTerm::third_section;
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            18 => match parser.lookahead() {
                Token::END => parser.reduce(5, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::first_section) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::SECTION_SPLIT) =
                            right.pop().unwrap()
                        {
                            if let parser::StackElement::NonTerminal(NonTerm::second_section) =
                                right.pop().unwrap()
                            {
                                if let parser::StackElement::Token(Token::SECTION_SPLIT) =
                                    right.pop().unwrap()
                                {
                                    if let parser::StackElement::NonTerminal(
                                        NonTerm::third_section,
                                    ) = right.pop().unwrap()
                                    {
                                        let mut arg0 = ();
                                        let mut arg1 = ();
                                        let mut arg2 = ();
                                        let mut arg3 = ();
                                        let mut arg4 = ();

                                        return NonTerm::doc;
                                    }
                                }
                            }
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            19 => match parser.lookahead() {
                Token::SECTION_SPLIT => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::term) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::terms) =
                            right.pop().unwrap()
                        {
                            let mut arg0 = ();
                            let mut arg1 = ();

                            return NonTerm::terms;
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location("<filename>", input, "Unexpected token"),
            },

            20 => match parser.lookahead() {
                Token::SECTION_SPLIT => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::prop) = right.pop().unwrap() {
                        if let parser::StackElement::NonTerminal(NonTerm::props) =
                            right.pop().unwrap()
                        {
                            let mut arg0 = ();
                            let mut arg1 = ();

                            return NonTerm::props;
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
