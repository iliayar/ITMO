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
    LITERAL(String),
    BRACKET_CODE(String),
    PLAIN_CODE(String),
    SEMICOLON,
    COLON,
    RULE_DIV,
    END,
    IDENT(String),
    PROP(String),
    SECTION_SPLIT,
}

#[derive(Debug)]
pub enum NonTerm {
    RULE_RIGHTS(Vec<(Vec<String>, Option<String>)>),
    PROP,
    SECTION1,
    DOC,
    SECTION3,
    PROPS,
    PROP_ARGS(Vec<String>),
    RULE,
    CODE(String),
    S,
    SECTION2,
    RULES,
    RULE_RIGHT_IDENTS(Vec<String>),
    RULE_RIGHT((Vec<String>, Option<String>)),
}

pub fn parse(input: &str) -> driver::gramma::Gramma {
    let mut gramma = driver::gramma::GrammaBuilder::new();

    let mut lexems = lexer::Lexer::new(Token::END);
    lexems.add("\\s", |s| None);
    lexems.add("%%\\n", |s| Some(Token::SECTION_SPLIT));
    lexems.add("\"([^\"\\\\]|\\\\[\\s\\S])*\"", |s| Some(Token::LITERAL(s)));
    lexems.add("%\\{(?:(?!%\\})(.|\n))+%\\}", |s| {
        Some(Token::PLAIN_CODE(s[2..s.len() - 2].to_string()))
    });
    lexems.add("\\{([^\\{\\}\\\\]|\\\\[\\s\\S])*(\\{([^\\{\\}\\\\]|\\\\[\\s\\S])*\\}|([^\\{\\}\\\\]|\\\\[\\s\\S])*)*\\}", |s| { Some(Token::BRACKET_CODE(s)) });
    lexems.add("%[a-zA-Z0_-]+", |s| Some(Token::PROP(s)));
    lexems.add("[a-zA-Z_-]+", |s| Some(Token::IDENT(s)));
    lexems.add("\\|", |s| Some(Token::RULE_DIV));
    lexems.add(";", |s| Some(Token::SEMICOLON));
    lexems.add(":", |s| Some(Token::COLON));

    let tokens = match lexems.lex(input) {
        Ok(res) => res,
        Err(lex_err) => {
            prety_print_lex_error("stdin", input, lex_err);
            panic!("Failed to lex file");
        }
    };

    let mut parser = parser::Parser::new(tokens, |state, nt| match state {
        0 => match nt {
            NonTerm::PROP => Some(1),
            NonTerm::SECTION1 => Some(2),
            NonTerm::CODE(_) => Some(5),
            NonTerm::PROPS => Some(4),
            NonTerm::DOC => Some(3),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        1 => match nt {
            NonTerm::PROP => Some(1),
            NonTerm::PROPS => Some(34),
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
            NonTerm::PROPS => Some(13),
            NonTerm::PROP => Some(1),
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
            NonTerm::PROP_ARGS(_) => Some(9),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        9 => match nt {
            NonTerm::CODE(_) => Some(10),
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
            NonTerm::RULE => Some(15),
            NonTerm::CODE(_) => Some(16),
            NonTerm::RULES => Some(18),
            NonTerm::SECTION2 => Some(17),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        15 => match nt {
            NonTerm::RULES => Some(33),
            NonTerm::RULE => Some(15),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        16 => match nt {
            NonTerm::RULE => Some(15),
            NonTerm::RULES => Some(32),
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
            NonTerm::RULE_RIGHTS(_) => Some(21),
            NonTerm::RULE_RIGHT_IDENTS(_) => Some(22),
            NonTerm::RULE_RIGHT(_) => Some(23),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        21 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        22 => match nt {
            NonTerm::CODE(_) => Some(24),
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

        25 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        26 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        27 => match nt {
            NonTerm::RULE_RIGHT_IDENTS(_) => Some(22),
            NonTerm::RULE_RIGHT(_) => Some(28),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        28 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        29 => match nt {
            NonTerm::CODE(_) => Some(31),
            NonTerm::SECTION3 => Some(30),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        30 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        31 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        32 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        33 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        34 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        _ => unreachable!(),
    });

    while !parser.accepted() {
        parser::print_parser_state(&parser);
        match parser.state() {

0 => match parser.lookahead() {
Token::PROP(_) => parser.shift(8),
Token::BRACKET_CODE(_) => parser.shift(6),
Token::SECTION_SPLIT => parser.reduce(0, |right| {
let mut right = right;



return NonTerm::PROPS;
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.shift(7),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

1 => match parser.lookahead() {
Token::PROP(_) => parser.shift(8),
Token::SECTION_SPLIT => parser.reduce(0, |right| {
let mut right = right;



return NonTerm::PROPS;
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

2 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.shift(14),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

3 => match parser.lookahead() {
Token::END => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::DOC) = right.pop().unwrap() {
let mut arg0 = ();

return NonTerm::S;
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

4 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROPS) = right.pop().unwrap() {
let mut arg0 = ();

return NonTerm::SECTION1;
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

5 => match parser.lookahead() {
Token::PROP(_) => parser.shift(8),
Token::SECTION_SPLIT => parser.reduce(0, |right| {
let mut right = right;



return NonTerm::PROPS;
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

6 => match parser.lookahead() {
Token::LITERAL(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::CODE(arg0);
}

return NonTerm::CODE(todo!("Implement for rule: CODE -> BRACKET_CODE"));
}
unreachable!();
}),
Token::SEMICOLON => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::CODE(arg0);
}

return NonTerm::CODE(todo!("Implement for rule: CODE -> BRACKET_CODE"));
}
unreachable!();
}),
Token::END => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::CODE(arg0);
}

return NonTerm::CODE(todo!("Implement for rule: CODE -> BRACKET_CODE"));
}
unreachable!();
}),
Token::SECTION_SPLIT => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::CODE(arg0);
}

return NonTerm::CODE(todo!("Implement for rule: CODE -> BRACKET_CODE"));
}
unreachable!();
}),
Token::PROP(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::CODE(arg0);
}

return NonTerm::CODE(todo!("Implement for rule: CODE -> BRACKET_CODE"));
}
unreachable!();
}),
Token::RULE_DIV => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::CODE(arg0);
}

return NonTerm::CODE(todo!("Implement for rule: CODE -> BRACKET_CODE"));
}
unreachable!();
}),
Token::IDENT(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::CODE(arg0);
}

return NonTerm::CODE(todo!("Implement for rule: CODE -> BRACKET_CODE"));
}
unreachable!();
}),
Token::BRACKET_CODE(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::CODE(arg0);
}

return NonTerm::CODE(todo!("Implement for rule: CODE -> BRACKET_CODE"));
}
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::CODE(arg0);
}

return NonTerm::CODE(todo!("Implement for rule: CODE -> BRACKET_CODE"));
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

7 => match parser.lookahead() {
Token::BRACKET_CODE(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::CODE(arg0);
}

return NonTerm::CODE(todo!("Implement for rule: CODE -> PLAIN_CODE"));
}
unreachable!();
}),
Token::LITERAL(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::CODE(arg0);
}

return NonTerm::CODE(todo!("Implement for rule: CODE -> PLAIN_CODE"));
}
unreachable!();
}),
Token::PROP(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::CODE(arg0);
}

return NonTerm::CODE(todo!("Implement for rule: CODE -> PLAIN_CODE"));
}
unreachable!();
}),
Token::IDENT(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::CODE(arg0);
}

return NonTerm::CODE(todo!("Implement for rule: CODE -> PLAIN_CODE"));
}
unreachable!();
}),
Token::RULE_DIV => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::CODE(arg0);
}

return NonTerm::CODE(todo!("Implement for rule: CODE -> PLAIN_CODE"));
}
unreachable!();
}),
Token::END => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::CODE(arg0);
}

return NonTerm::CODE(todo!("Implement for rule: CODE -> PLAIN_CODE"));
}
unreachable!();
}),
Token::SECTION_SPLIT => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::CODE(arg0);
}

return NonTerm::CODE(todo!("Implement for rule: CODE -> PLAIN_CODE"));
}
unreachable!();
}),
Token::SEMICOLON => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::CODE(arg0);
}

return NonTerm::CODE(todo!("Implement for rule: CODE -> PLAIN_CODE"));
}
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::CODE(arg0);
}

return NonTerm::CODE(todo!("Implement for rule: CODE -> PLAIN_CODE"));
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

8 => match parser.lookahead() {
Token::PLAIN_CODE(_) => parser.reduce(0, |right| {
let mut right = right;



{
return NonTerm::PROP_ARGS(Vec::new());
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS ->"));
unreachable!();
}),
Token::LITERAL(_) => parser.reduce(0, |right| {
let mut right = right;



{
return NonTerm::PROP_ARGS(Vec::new());
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS ->"));
unreachable!();
}),
Token::IDENT(_) => parser.reduce(0, |right| {
let mut right = right;



{
return NonTerm::PROP_ARGS(Vec::new());
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS ->"));
unreachable!();
}),
Token::PROP(_) => parser.reduce(0, |right| {
let mut right = right;



{
return NonTerm::PROP_ARGS(Vec::new());
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS ->"));
unreachable!();
}),
Token::SECTION_SPLIT => parser.reduce(0, |right| {
let mut right = right;



{
return NonTerm::PROP_ARGS(Vec::new());
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS ->"));
unreachable!();
}),
Token::BRACKET_CODE(_) => parser.reduce(0, |right| {
let mut right = right;



{
return NonTerm::PROP_ARGS(Vec::new());
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS ->"));
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

9 => match parser.lookahead() {
Token::IDENT(_) => parser.shift(12),
Token::SECTION_SPLIT => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PROP(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
gramma.add_prop(arg0, arg1);
}

return NonTerm::PROP;
}
}
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.shift(7),
Token::LITERAL(_) => parser.shift(11),
Token::PROP(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PROP(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
gramma.add_prop(arg0, arg1);
}

return NonTerm::PROP;
}
}
unreachable!();
}),
Token::BRACKET_CODE(_) => parser.shift(6),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

10 => match parser.lookahead() {
Token::LITERAL(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::CODE(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1);
return NonTerm::PROP_ARGS(arg0);
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS -> PROP_ARGS CODE"));
}
}
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::CODE(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1);
return NonTerm::PROP_ARGS(arg0);
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS -> PROP_ARGS CODE"));
}
}
unreachable!();
}),
Token::IDENT(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::CODE(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1);
return NonTerm::PROP_ARGS(arg0);
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS -> PROP_ARGS CODE"));
}
}
unreachable!();
}),
Token::BRACKET_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::CODE(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1);
return NonTerm::PROP_ARGS(arg0);
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS -> PROP_ARGS CODE"));
}
}
unreachable!();
}),
Token::PROP(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::CODE(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1);
return NonTerm::PROP_ARGS(arg0);
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS -> PROP_ARGS CODE"));
}
}
unreachable!();
}),
Token::SECTION_SPLIT => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::CODE(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1);
return NonTerm::PROP_ARGS(arg0);
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS -> PROP_ARGS CODE"));
}
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

11 => match parser.lookahead() {
Token::BRACKET_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::LITERAL(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1.trim_matches('"').to_string());
return NonTerm::PROP_ARGS(arg0);
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS -> PROP_ARGS LITERAL"));
}
}
unreachable!();
}),
Token::PROP(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::LITERAL(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1.trim_matches('"').to_string());
return NonTerm::PROP_ARGS(arg0);
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS -> PROP_ARGS LITERAL"));
}
}
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::LITERAL(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1.trim_matches('"').to_string());
return NonTerm::PROP_ARGS(arg0);
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS -> PROP_ARGS LITERAL"));
}
}
unreachable!();
}),
Token::LITERAL(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::LITERAL(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1.trim_matches('"').to_string());
return NonTerm::PROP_ARGS(arg0);
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS -> PROP_ARGS LITERAL"));
}
}
unreachable!();
}),
Token::SECTION_SPLIT => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::LITERAL(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1.trim_matches('"').to_string());
return NonTerm::PROP_ARGS(arg0);
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS -> PROP_ARGS LITERAL"));
}
}
unreachable!();
}),
Token::IDENT(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::LITERAL(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1.trim_matches('"').to_string());
return NonTerm::PROP_ARGS(arg0);
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS -> PROP_ARGS LITERAL"));
}
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

12 => match parser.lookahead() {
Token::BRACKET_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1);
return NonTerm::PROP_ARGS(arg0);
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS -> PROP_ARGS IDENT"));
}
}
unreachable!();
}),
Token::PROP(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1);
return NonTerm::PROP_ARGS(arg0);
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS -> PROP_ARGS IDENT"));
}
}
unreachable!();
}),
Token::SECTION_SPLIT => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1);
return NonTerm::PROP_ARGS(arg0);
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS -> PROP_ARGS IDENT"));
}
}
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1);
return NonTerm::PROP_ARGS(arg0);
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS -> PROP_ARGS IDENT"));
}
}
unreachable!();
}),
Token::LITERAL(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1);
return NonTerm::PROP_ARGS(arg0);
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS -> PROP_ARGS IDENT"));
}
}
unreachable!();
}),
Token::IDENT(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP_ARGS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1);
return NonTerm::PROP_ARGS(arg0);
}

return NonTerm::PROP_ARGS(todo!("Implement for rule: PROP_ARGS -> PROP_ARGS IDENT"));
}
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

13 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::CODE(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::PROPS) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = ();

{
gramma.header(arg0);
}

return NonTerm::SECTION1;
}
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

14 => match parser.lookahead() {
Token::BRACKET_CODE(_) => parser.shift(6),
Token::SECTION_SPLIT => parser.reduce(0, |right| {
let mut right = right;



return NonTerm::RULES;
unreachable!();
}),
Token::IDENT(_) => parser.shift(19),
Token::PLAIN_CODE(_) => parser.shift(7),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

15 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(0, |right| {
let mut right = right;



return NonTerm::RULES;
unreachable!();
}),
Token::IDENT(_) => parser.shift(19),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

16 => match parser.lookahead() {
Token::IDENT(_) => parser.shift(19),
Token::SECTION_SPLIT => parser.reduce(0, |right| {
let mut right = right;



return NonTerm::RULES;
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

17 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.shift(29),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

18 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::RULES) = right.pop().unwrap() {
let mut arg0 = ();

return NonTerm::SECTION2;
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

19 => match parser.lookahead() {
Token::COLON => parser.shift(20),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

20 => match parser.lookahead() {
Token::PLAIN_CODE(_) => parser.reduce(0, |right| {
let mut right = right;



{
return NonTerm::RULE_RIGHT_IDENTS(Vec::new());
}

return NonTerm::RULE_RIGHT_IDENTS(todo!("Implement for rule: RULE_RIGHT_IDENTS ->"));
unreachable!();
}),
Token::IDENT(_) => parser.reduce(0, |right| {
let mut right = right;



{
return NonTerm::RULE_RIGHT_IDENTS(Vec::new());
}

return NonTerm::RULE_RIGHT_IDENTS(todo!("Implement for rule: RULE_RIGHT_IDENTS ->"));
unreachable!();
}),
Token::BRACKET_CODE(_) => parser.reduce(0, |right| {
let mut right = right;



{
return NonTerm::RULE_RIGHT_IDENTS(Vec::new());
}

return NonTerm::RULE_RIGHT_IDENTS(todo!("Implement for rule: RULE_RIGHT_IDENTS ->"));
unreachable!();
}),
Token::RULE_DIV => parser.reduce(0, |right| {
let mut right = right;



{
return NonTerm::RULE_RIGHT_IDENTS(Vec::new());
}

return NonTerm::RULE_RIGHT_IDENTS(todo!("Implement for rule: RULE_RIGHT_IDENTS ->"));
unreachable!();
}),
Token::SEMICOLON => parser.reduce(0, |right| {
let mut right = right;



{
return NonTerm::RULE_RIGHT_IDENTS(Vec::new());
}

return NonTerm::RULE_RIGHT_IDENTS(todo!("Implement for rule: RULE_RIGHT_IDENTS ->"));
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

21 => match parser.lookahead() {
Token::SEMICOLON => parser.shift(26),
Token::RULE_DIV => parser.shift(27),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

22 => match parser.lookahead() {
Token::RULE_DIV => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::RULE_RIGHT_IDENTS(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::RULE_RIGHT((arg0, None))
}

return NonTerm::RULE_RIGHT(todo!("Implement for rule: RULE_RIGHT -> RULE_RIGHT_IDENTS"));
}
unreachable!();
}),
Token::BRACKET_CODE(_) => parser.shift(6),
Token::PLAIN_CODE(_) => parser.shift(7),
Token::SEMICOLON => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::RULE_RIGHT_IDENTS(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::RULE_RIGHT((arg0, None))
}

return NonTerm::RULE_RIGHT(todo!("Implement for rule: RULE_RIGHT -> RULE_RIGHT_IDENTS"));
}
unreachable!();
}),
Token::IDENT(_) => parser.shift(25),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

23 => match parser.lookahead() {
Token::RULE_DIV => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::RULE_RIGHT(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::RULE_RIGHTS(vec![arg0])
}

return NonTerm::RULE_RIGHTS(todo!("Implement for rule: RULE_RIGHTS -> RULE_RIGHT"));
}
unreachable!();
}),
Token::SEMICOLON => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::RULE_RIGHT(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
return NonTerm::RULE_RIGHTS(vec![arg0])
}

return NonTerm::RULE_RIGHTS(todo!("Implement for rule: RULE_RIGHTS -> RULE_RIGHT"));
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

24 => match parser.lookahead() {
Token::SEMICOLON => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::RULE_RIGHT_IDENTS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::CODE(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
return NonTerm::RULE_RIGHT((arg0, Some(arg1)))
}

return NonTerm::RULE_RIGHT(todo!("Implement for rule: RULE_RIGHT -> RULE_RIGHT_IDENTS CODE"));
}
}
unreachable!();
}),
Token::RULE_DIV => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::RULE_RIGHT_IDENTS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::CODE(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
return NonTerm::RULE_RIGHT((arg0, Some(arg1)))
}

return NonTerm::RULE_RIGHT(todo!("Implement for rule: RULE_RIGHT -> RULE_RIGHT_IDENTS CODE"));
}
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

25 => match parser.lookahead() {
Token::PLAIN_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::RULE_RIGHT_IDENTS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1);
return NonTerm::RULE_RIGHT_IDENTS(arg0);
}

return NonTerm::RULE_RIGHT_IDENTS(todo!("Implement for rule: RULE_RIGHT_IDENTS -> RULE_RIGHT_IDENTS IDENT"));
}
}
unreachable!();
}),
Token::BRACKET_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::RULE_RIGHT_IDENTS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1);
return NonTerm::RULE_RIGHT_IDENTS(arg0);
}

return NonTerm::RULE_RIGHT_IDENTS(todo!("Implement for rule: RULE_RIGHT_IDENTS -> RULE_RIGHT_IDENTS IDENT"));
}
}
unreachable!();
}),
Token::RULE_DIV => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::RULE_RIGHT_IDENTS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1);
return NonTerm::RULE_RIGHT_IDENTS(arg0);
}

return NonTerm::RULE_RIGHT_IDENTS(todo!("Implement for rule: RULE_RIGHT_IDENTS -> RULE_RIGHT_IDENTS IDENT"));
}
}
unreachable!();
}),
Token::SEMICOLON => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::RULE_RIGHT_IDENTS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1);
return NonTerm::RULE_RIGHT_IDENTS(arg0);
}

return NonTerm::RULE_RIGHT_IDENTS(todo!("Implement for rule: RULE_RIGHT_IDENTS -> RULE_RIGHT_IDENTS IDENT"));
}
}
unreachable!();
}),
Token::IDENT(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::RULE_RIGHT_IDENTS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;

{
arg0.push(arg1);
return NonTerm::RULE_RIGHT_IDENTS(arg0);
}

return NonTerm::RULE_RIGHT_IDENTS(todo!("Implement for rule: RULE_RIGHT_IDENTS -> RULE_RIGHT_IDENTS IDENT"));
}
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

26 => match parser.lookahead() {
Token::IDENT(_) => parser.reduce(4, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::COLON) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::RULE_RIGHTS(arg2)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::SEMICOLON) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = ();
let mut arg2 = arg2;
let mut arg3 = ();

{
gramma.add_rule_with_eval(arg0, arg2);
}

return NonTerm::RULE;
}
}
}
}
unreachable!();
}),
Token::SECTION_SPLIT => parser.reduce(4, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::COLON) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::RULE_RIGHTS(arg2)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::SEMICOLON) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = ();
let mut arg2 = arg2;
let mut arg3 = ();

{
gramma.add_rule_with_eval(arg0, arg2);
}

return NonTerm::RULE;
}
}
}
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

27 => match parser.lookahead() {
Token::BRACKET_CODE(_) => parser.reduce(0, |right| {
let mut right = right;



{
return NonTerm::RULE_RIGHT_IDENTS(Vec::new());
}

return NonTerm::RULE_RIGHT_IDENTS(todo!("Implement for rule: RULE_RIGHT_IDENTS ->"));
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.reduce(0, |right| {
let mut right = right;



{
return NonTerm::RULE_RIGHT_IDENTS(Vec::new());
}

return NonTerm::RULE_RIGHT_IDENTS(todo!("Implement for rule: RULE_RIGHT_IDENTS ->"));
unreachable!();
}),
Token::IDENT(_) => parser.reduce(0, |right| {
let mut right = right;



{
return NonTerm::RULE_RIGHT_IDENTS(Vec::new());
}

return NonTerm::RULE_RIGHT_IDENTS(todo!("Implement for rule: RULE_RIGHT_IDENTS ->"));
unreachable!();
}),
Token::RULE_DIV => parser.reduce(0, |right| {
let mut right = right;



{
return NonTerm::RULE_RIGHT_IDENTS(Vec::new());
}

return NonTerm::RULE_RIGHT_IDENTS(todo!("Implement for rule: RULE_RIGHT_IDENTS ->"));
unreachable!();
}),
Token::SEMICOLON => parser.reduce(0, |right| {
let mut right = right;



{
return NonTerm::RULE_RIGHT_IDENTS(Vec::new());
}

return NonTerm::RULE_RIGHT_IDENTS(todo!("Implement for rule: RULE_RIGHT_IDENTS ->"));
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

28 => match parser.lookahead() {
Token::SEMICOLON => parser.reduce(3, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::RULE_RIGHTS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::RULE_DIV) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::RULE_RIGHT(arg2)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = ();
let mut arg2 = arg2;

{
arg0.push(arg2);
return NonTerm::RULE_RIGHTS(arg0);
}

return NonTerm::RULE_RIGHTS(todo!("Implement for rule: RULE_RIGHTS -> RULE_RIGHTS RULE_DIV RULE_RIGHT"));
}
}
}
unreachable!();
}),
Token::RULE_DIV => parser.reduce(3, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::RULE_RIGHTS(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::RULE_DIV) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::RULE_RIGHT(arg2)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = ();
let mut arg2 = arg2;

{
arg0.push(arg2);
return NonTerm::RULE_RIGHTS(arg0);
}

return NonTerm::RULE_RIGHTS(todo!("Implement for rule: RULE_RIGHTS -> RULE_RIGHTS RULE_DIV RULE_RIGHT"));
}
}
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

29 => match parser.lookahead() {
Token::BRACKET_CODE(_) => parser.shift(6),
Token::PLAIN_CODE(_) => parser.shift(7),
Token::END => parser.reduce(0, |right| {
let mut right = right;



return NonTerm::SECTION3;
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

30 => match parser.lookahead() {
Token::END => parser.reduce(5, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::SECTION1) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::SECTION_SPLIT) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::SECTION2) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::SECTION_SPLIT) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::SECTION3) = right.pop().unwrap() {
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

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

31 => match parser.lookahead() {
Token::END => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;

{
gramma.fin_code(arg0);
}

return NonTerm::SECTION3;
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

32 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::CODE(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::RULES) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = ();

{
gramma.init_code(arg0);
}

return NonTerm::SECTION2;
}
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

33 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::RULE) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::RULES) = right.pop().unwrap() {
let mut arg0 = ();
let mut arg1 = ();

return NonTerm::RULES;
}
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

34 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::PROP) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::PROPS) = right.pop().unwrap() {
let mut arg0 = ();
let mut arg1 = ();

return NonTerm::PROPS;
}
}
unreachable!();
}),

    _ => parser.panic_location("<filename>", input, "Unexpected token")
},

        _ => parser.panic_location("<filename>", input, "Unexpected token")
    }
    }

    return gramma.build();
}
