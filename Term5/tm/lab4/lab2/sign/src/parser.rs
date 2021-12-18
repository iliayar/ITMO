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

use super::{NodeValue, Tree};

#[derive(Debug)]
pub enum Token {
    RPAREN,
    SEMICOLON,
    LPAREN,
    IDENTIFIER(String),
    COMMA,
    END,
    ASTERISK,
}

#[derive(Debug)]
pub enum NonTerm {
    arg(Tree),
    pointer(Tree),
    args(Tree),
    S,
    inp,
    declaration(Tree),
    args_rest(Tree),
}

pub fn parse(input: &str) -> Tree {
    let mut res: Option<Tree> = None;

    let mut lexems = lexer::Lexer::new(Token::END);
    lexems.add("\\s", |s| None);
    lexems.add("[a-zA-Z_][a-zA-Z_0-9]*", |s| Some(Token::IDENTIFIER(s)));
    lexems.add("\\*", |s| Some(Token::ASTERISK));
    lexems.add(";", |s| Some(Token::SEMICOLON));
    lexems.add(",", |s| Some(Token::COMMA));
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
            NonTerm::inp => Some(1),
            NonTerm::declaration(_) => Some(2),
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
            NonTerm::pointer(_) => Some(4),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        4 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        5 => match nt {
            NonTerm::pointer(_) => Some(6),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        6 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        7 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        8 => match nt {
            NonTerm::arg(_) => Some(9),
            NonTerm::args(_) => Some(10),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        9 => match nt {
            NonTerm::args_rest(_) => Some(16),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        10 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        11 => match nt {
            NonTerm::pointer(_) => Some(12),
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
            NonTerm::arg(_) => Some(18),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        18 => match nt {
            NonTerm::args_rest(_) => Some(19),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        19 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        _ => unreachable!(),
    });

    while !parser.accepted() {
        parser::print_parser_state(&parser);

        match parser.state() {

0 => match parser.lookahead() {
Token::IDENTIFIER(_) => parser.shift(3),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
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

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

2 => match parser.lookahead() {
Token::END => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::declaration(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ res = Some(arg0); }
return NonTerm::inp;
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

3 => match parser.lookahead() {
Token::IDENTIFIER(_) => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::pointer(Tree::node(NodeValue::NonTerminal("ASTERISL".to_string()))); }
return NonTerm::pointer(todo!("Implement for rule: pointer ->"));
unreachable!();
}),
Token::ASTERISK => parser.shift(5),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

4 => match parser.lookahead() {
Token::IDENTIFIER(_) => parser.shift(7),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

5 => match parser.lookahead() {
Token::ASTERISK => parser.shift(5),
Token::IDENTIFIER(_) => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::pointer(Tree::node(NodeValue::NonTerminal("ASTERISL".to_string()))); }
return NonTerm::pointer(todo!("Implement for rule: pointer ->"));
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

6 => match parser.lookahead() {
Token::IDENTIFIER(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::ASTERISK) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::pointer(arg1)) = right.pop().unwrap() {
let mut arg0 = ();
let mut arg1 = arg1;
{ return NonTerm::pointer(Tree::new(NodeValue::NonTerminal("POINTER".to_string()), vec![
					    Tree::node(NodeValue::Terminal(super::Token::ASTERISK)),
					    arg1,
                                       ]))}
return NonTerm::pointer(todo!("Implement for rule: pointer -> ASTERISK pointer"));
}
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

7 => match parser.lookahead() {
Token::LPAREN => parser.shift(8),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

8 => match parser.lookahead() {
Token::RPAREN => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::args(Tree::node(NodeValue::NonTerminal("ARGS".to_string()))); }
return NonTerm::args(todo!("Implement for rule: args ->"));
unreachable!();
}),
Token::IDENTIFIER(_) => parser.shift(11),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

9 => match parser.lookahead() {
Token::COMMA => parser.shift(17),
Token::RPAREN => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::args_rest(Tree::node(NodeValue::NonTerminal("ARGS_REST".to_string()))); }
return NonTerm::args_rest(todo!("Implement for rule: args_rest ->"));
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

10 => match parser.lookahead() {
Token::RPAREN => parser.shift(14),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

11 => match parser.lookahead() {
Token::ASTERISK => parser.shift(5),
Token::IDENTIFIER(_) => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::pointer(Tree::node(NodeValue::NonTerminal("ASTERISL".to_string()))); }
return NonTerm::pointer(todo!("Implement for rule: pointer ->"));
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

12 => match parser.lookahead() {
Token::IDENTIFIER(_) => parser.shift(13),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

13 => match parser.lookahead() {
Token::RPAREN => parser.reduce(3, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::IDENTIFIER(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::pointer(arg1)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENTIFIER(arg2)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
let mut arg2 = arg2;
{
        return NonTerm::arg(Tree::new(NodeValue::NonTerminal("ARG".to_string()), vec! [
					    Tree::node(NodeValue::Terminal(super::Token::IDENTIFIER(arg0))),
					    arg1,
					    Tree::node(NodeValue::Terminal(super::Token::IDENTIFIER(arg2))),
                                                  ]))
    }
return NonTerm::arg(todo!("Implement for rule: arg -> IDENTIFIER pointer IDENTIFIER"));
}
}
}
unreachable!();
}),
Token::COMMA => parser.reduce(3, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::IDENTIFIER(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::pointer(arg1)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENTIFIER(arg2)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
let mut arg2 = arg2;
{
        return NonTerm::arg(Tree::new(NodeValue::NonTerminal("ARG".to_string()), vec! [
					    Tree::node(NodeValue::Terminal(super::Token::IDENTIFIER(arg0))),
					    arg1,
					    Tree::node(NodeValue::Terminal(super::Token::IDENTIFIER(arg2))),
                                                  ]))
    }
return NonTerm::arg(todo!("Implement for rule: arg -> IDENTIFIER pointer IDENTIFIER"));
}
}
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

14 => match parser.lookahead() {
Token::SEMICOLON => parser.shift(15),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

15 => match parser.lookahead() {
Token::END => parser.reduce(7, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::IDENTIFIER(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::pointer(arg1)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENTIFIER(arg2)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::LPAREN) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::args(arg4)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::RPAREN) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::SEMICOLON) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
let mut arg2 = arg2;
let mut arg3 = ();
let mut arg4 = arg4;
let mut arg5 = ();
let mut arg6 = ();
{
		    return NonTerm::declaration(Tree::new(NodeValue::NonTerminal("DECLARATION".to_string()), vec![
					    Tree::node(NodeValue::Terminal(super::Token::IDENTIFIER(arg0))),
					    arg1,
					    Tree::node(NodeValue::Terminal(super::Token::IDENTIFIER(arg2))),
					    Tree::node(NodeValue::Terminal(super::Token::LPAREN)),
					    arg4,
					    Tree::node(NodeValue::Terminal(super::Token::RPAREN)),
					    Tree::node(NodeValue::Terminal(super::Token::SEMICOLON)),
                                            ]))
                }
return NonTerm::declaration(todo!("Implement for rule: declaration -> IDENTIFIER pointer IDENTIFIER LPAREN args RPAREN SEMICOLON"));
}
}
}
}
}
}
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

16 => match parser.lookahead() {
Token::RPAREN => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::arg(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::args_rest(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
         return NonTerm::args(Tree::new(NodeValue::NonTerminal("ARGS".to_string()), vec![ arg0, arg1 ]));
     }
return NonTerm::args(todo!("Implement for rule: args -> arg args_rest"));
}
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

17 => match parser.lookahead() {
Token::IDENTIFIER(_) => parser.shift(11),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

18 => match parser.lookahead() {
Token::RPAREN => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::args_rest(Tree::node(NodeValue::NonTerminal("ARGS_REST".to_string()))); }
return NonTerm::args_rest(todo!("Implement for rule: args_rest ->"));
unreachable!();
}),
Token::COMMA => parser.shift(17),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

19 => match parser.lookahead() {
Token::RPAREN => parser.reduce(3, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::COMMA) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::arg(arg1)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::args_rest(arg2)) = right.pop().unwrap() {
let mut arg0 = ();
let mut arg1 = arg1;
let mut arg2 = arg2;
{
              return NonTerm::args_rest(Tree::new(NodeValue::NonTerminal("ARGS_REST".to_string()), vec![
                                  Tree::node(NodeValue::Terminal(super::Token::COMMA)),
				  arg1,
				  arg2,
                                  ]));
          }
return NonTerm::args_rest(todo!("Implement for rule: args_rest -> COMMA arg args_rest"));
}
}
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

        _ => parser.panic_location("<filename>", input, "Unexpected token")
    }
    }

    return res.unwrap();
}
