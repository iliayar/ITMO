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

#[derive(Debug)]
pub enum Token {
    PLUS,
    MULT,
    DIV,
    FACTORIAL,
    MINUS,
    RPAREN,
    NUM(i64),
    LPAREN,
    SEMICOLON,
    END,
}

#[derive(Debug)]
pub enum NonTerm {
    expr(i64),
    inp,
    S,
    expr_line,
}

pub fn get_lexems() -> lexer::Lexer<Token> {
    let mut lexems = lexer::Lexer::new(Token::END);
    lexems.add("\\s", |s| None);
    lexems.add("[0-9]+", |s| Some(Token::NUM(s.parse().unwrap())));
    lexems.add(";", |s| Some(Token::SEMICOLON));
    lexems.add("!", |s| Some(Token::FACTORIAL));
    lexems.add("\\+", |s| Some(Token::PLUS));
    lexems.add("-", |s| Some(Token::MINUS));
    lexems.add("\\*", |s| Some(Token::MULT));
    lexems.add("/", |s| Some(Token::DIV));
    lexems.add("\\(", |s| Some(Token::LPAREN));
    lexems.add("\\)", |s| Some(Token::RPAREN));

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
    let mut parser = parser::Parser::new(tokens, |state, nt| match state {
        0 => match nt {
            NonTerm::expr(_) => Some(1),
            NonTerm::expr_line => Some(3),
            NonTerm::inp => Some(2),
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
            NonTerm::expr(_) => Some(18),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        5 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        6 => match nt {
            NonTerm::expr(_) => Some(7),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        7 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        8 => match nt {
            NonTerm::expr(_) => Some(17),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        9 => match nt {
            NonTerm::expr(_) => Some(16),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        10 => match nt {
            NonTerm::expr(_) => Some(15),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        11 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        12 => match nt {
            NonTerm::expr(_) => Some(14),
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
            NonTerm::S => None,
            _ => unreachable!(),
        },

        18 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        19 => match nt {
            NonTerm::inp => Some(20),
            NonTerm::expr_line => Some(3),
            NonTerm::expr(_) => Some(1),
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
                Token::LPAREN => parser.shift(6),
                Token::MINUS => parser.shift(4),
                Token::END => parser.reduce(0, |right| {
                    let mut right = right;

                    return NonTerm::inp;
                    unreachable!();
                }),
                Token::NUM(_) => parser.shift(5),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            1 => match parser.lookahead() {
                Token::MULT => parser.shift(9),
                Token::MINUS => parser.shift(12),
                Token::SEMICOLON => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        let mut arg0 = arg0;
                        {
                            println!("{}", arg0);
                        }
                        return NonTerm::expr_line;
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.shift(8),
                Token::FACTORIAL => parser.shift(11),
                Token::DIV => parser.shift(10),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            2 => match parser.lookahead() {
                Token::END => parser.reduce(1, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::inp) = right.pop().unwrap() {
                        let mut arg0 = ();

                        return NonTerm::S;
                    }
                    unreachable!();
                }),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            3 => match parser.lookahead() {
                Token::SEMICOLON => parser.shift(19),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            4 => match parser.lookahead() {
                Token::NUM(_) => parser.shift(5),
                Token::MINUS => parser.shift(4),
                Token::LPAREN => parser.shift(6),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            5 => match parser.lookahead() {
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
                Token::FACTORIAL => parser.reduce(1, |right| {
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
                Token::MINUS => parser.shift(4),
                Token::NUM(_) => parser.shift(5),
                Token::LPAREN => parser.shift(6),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            7 => match parser.lookahead() {
                Token::MULT => parser.shift(9),
                Token::DIV => parser.shift(10),
                Token::PLUS => parser.shift(8),
                Token::FACTORIAL => parser.shift(11),
                Token::MINUS => parser.shift(12),
                Token::RPAREN => parser.shift(13),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            8 => match parser.lookahead() {
                Token::MINUS => parser.shift(4),
                Token::LPAREN => parser.shift(6),
                Token::NUM(_) => parser.shift(5),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            9 => match parser.lookahead() {
                Token::MINUS => parser.shift(4),
                Token::NUM(_) => parser.shift(5),
                Token::LPAREN => parser.shift(6),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            10 => match parser.lookahead() {
                Token::MINUS => parser.shift(4),
                Token::NUM(_) => parser.shift(5),
                Token::LPAREN => parser.shift(6),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            11 => match parser.lookahead() {
                Token::SEMICOLON => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::FACTORIAL) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = ();
                            {
                                return NonTerm::expr((1..=arg0).product());
                            }
                            return NonTerm::expr(todo!(
                                "Implement for rule: expr -> expr FACTORIAL"
                            ));
                        }
                    }
                    unreachable!();
                }),
                Token::DIV => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::FACTORIAL) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = ();
                            {
                                return NonTerm::expr((1..=arg0).product());
                            }
                            return NonTerm::expr(todo!(
                                "Implement for rule: expr -> expr FACTORIAL"
                            ));
                        }
                    }
                    unreachable!();
                }),
                Token::FACTORIAL => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::FACTORIAL) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = ();
                            {
                                return NonTerm::expr((1..=arg0).product());
                            }
                            return NonTerm::expr(todo!(
                                "Implement for rule: expr -> expr FACTORIAL"
                            ));
                        }
                    }
                    unreachable!();
                }),
                Token::PLUS => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::FACTORIAL) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = ();
                            {
                                return NonTerm::expr((1..=arg0).product());
                            }
                            return NonTerm::expr(todo!(
                                "Implement for rule: expr -> expr FACTORIAL"
                            ));
                        }
                    }
                    unreachable!();
                }),
                Token::MINUS => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::FACTORIAL) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = ();
                            {
                                return NonTerm::expr((1..=arg0).product());
                            }
                            return NonTerm::expr(todo!(
                                "Implement for rule: expr -> expr FACTORIAL"
                            ));
                        }
                    }
                    unreachable!();
                }),
                Token::MULT => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::FACTORIAL) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = ();
                            {
                                return NonTerm::expr((1..=arg0).product());
                            }
                            return NonTerm::expr(todo!(
                                "Implement for rule: expr -> expr FACTORIAL"
                            ));
                        }
                    }
                    unreachable!();
                }),
                Token::RPAREN => parser.reduce(2, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr(arg0)) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::FACTORIAL) = right.pop().unwrap()
                        {
                            let mut arg0 = arg0;
                            let mut arg1 = ();
                            {
                                return NonTerm::expr((1..=arg0).product());
                            }
                            return NonTerm::expr(todo!(
                                "Implement for rule: expr -> expr FACTORIAL"
                            ));
                        }
                    }
                    unreachable!();
                }),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            12 => match parser.lookahead() {
                Token::MINUS => parser.shift(4),
                Token::LPAREN => parser.shift(6),
                Token::NUM(_) => parser.shift(5),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            13 => match parser.lookahead() {
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
                Token::FACTORIAL => parser.reduce(3, |right| {
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

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            14 => match parser.lookahead() {
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
                Token::MULT => parser.shift(9),
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
                Token::FACTORIAL => parser.shift(11),
                Token::DIV => parser.shift(10),
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

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            15 => match parser.lookahead() {
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
                Token::FACTORIAL => parser.shift(11),
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

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            16 => match parser.lookahead() {
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
                Token::FACTORIAL => parser.shift(11),
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

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            17 => match parser.lookahead() {
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
                Token::DIV => parser.shift(10),
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
                Token::FACTORIAL => parser.shift(11),
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
                Token::MULT => parser.shift(9),
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

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            18 => match parser.lookahead() {
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
                Token::MULT => parser.shift(9),
                Token::FACTORIAL => parser.shift(11),
                Token::DIV => parser.shift(10),
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

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            19 => match parser.lookahead() {
                Token::END => parser.reduce(0, |right| {
                    let mut right = right;

                    return NonTerm::inp;
                    unreachable!();
                }),
                Token::NUM(_) => parser.shift(5),
                Token::MINUS => parser.shift(4),
                Token::LPAREN => parser.shift(6),

                _ => parser.panic_location(filename, "Unexpected token"),
            },

            20 => match parser.lookahead() {
                Token::END => parser.reduce(3, |right| {
                    let mut right = right;

                    if let parser::StackElement::NonTerminal(NonTerm::expr_line) =
                        right.pop().unwrap()
                    {
                        if let parser::StackElement::Token(Token::SEMICOLON) = right.pop().unwrap()
                        {
                            if let parser::StackElement::NonTerminal(NonTerm::inp) =
                                right.pop().unwrap()
                            {
                                let mut arg0 = ();
                                let mut arg1 = ();
                                let mut arg2 = ();

                                return NonTerm::inp;
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
