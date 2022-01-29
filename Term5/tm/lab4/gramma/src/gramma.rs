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

use super::driver;

#[derive(Debug)]
pub enum Token {
    COLON,
    SEMICOLON,
    LITERAL(String),
    ALIAS(String),
    PROP(String),
    IDENT(String),
    RULE_DIV,
    END,
    BRACKET_CODE(String),
    PLAIN_CODE(String),
    SECTION_SPLIT,
}

#[derive(Debug)]
pub enum NonTerm {
    prop,
    rule_right((Vec<String>, Option<String>)),
    section_third,
    props,
    prop_args(Vec<String>),
    rules,
    doc,
    section_second,
    rule,
    code(String),
    section_first,
    rule_right_idents(Vec<String>),
    rule_rights(Vec<(Vec<String>, Option<String>)>),
    S,
}

pub fn get_lexems() -> lexer::Lexer<Token> {
    let mut lexems = lexer::Lexer::new(Token::END);
    lexems.add("\\s", |s| None);
    lexems.add("%%\\n", |s| Some(Token::SECTION_SPLIT));
    lexems.add("[a-zA-Z_][a-zA-Z0-9_]*", |s| Some(Token::IDENT(s)));
    lexems.add("\"([^\"\\\\]|\\\\[\\s\\S])*\"", |s| {
        Some(Token::LITERAL(s[1..s.len() - 1].to_string()))
    });
    lexems.add("'([^'\\\\]|\\\\[\\s\\S])*'", |s| {
        Some(Token::ALIAS(s[1..s.len() - 1].to_string()))
    });
    lexems.add("%[a-zA-Z0-9_-]+", |s| Some(Token::PROP(s)));
    lexems.add("%\\{(?:(?!%\\})(.|\\n))+%\\}", |s| {
        Some(Token::PLAIN_CODE(s[2..s.len() - 2].to_string()))
    });
    lexems.add("\\{\\{(?:(?!\\}\\})(.|\\n))+\\}\\}", |s| {
        Some(Token::BRACKET_CODE(s[1..s.len() - 1].to_string()))
    });
    lexems.add("\\|", |s| Some(Token::RULE_DIV));
    lexems.add(";", |s| Some(Token::SEMICOLON));
    lexems.add(":", |s| Some(Token::COLON));

    return lexems;
}

pub fn parse_stream<R: BufRead>(filename: &str, stream: &mut R) -> driver::gramma::Gramma {
    let lexems = get_lexems();

    let tokens = lexems.lex_stream(stream, |lex_err, input| {
        prety_print_lex_error(filename, &input, lex_err);
        panic!("Failed to lex file");
    });

    return parse_token_stream(filename, tokens);
}

pub fn parse(filename: &str, input: &str) -> driver::gramma::Gramma {
    let lexems = get_lexems();

    let tokens = lexems.lex(input);

    if let Err(lex_err) = tokens {
        prety_print_lex_error(filename, &input, lex_err);
        panic!("Failed to lex file");
    } else {
        return parse_token_stream(filename, tokens.unwrap());
    }
}

pub fn parse_file(filename: &str) -> driver::gramma::Gramma {
    let input = std::fs::read_to_string(filename).expect("Failed to read file");

    return parse(filename, &input);
}

fn parse_token_stream<TS: parser::TokenStream<Token>>(
    filename: &str,
    tokens: TS,
) -> driver::gramma::Gramma {
    let mut builder = driver::gramma::GrammaBuilder::new();

    let mut parser = parser::Parser::new(tokens, |state, nt| match state {
        0 => match nt {
            NonTerm::props => Some(2),
            NonTerm::code(_) => Some(4),
            NonTerm::section_first => Some(5),
            NonTerm::prop => Some(1),
            NonTerm::doc => Some(3),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        1 => match nt {
            NonTerm::prop => Some(1),
            NonTerm::props => Some(36),
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
            NonTerm::prop => Some(1),
            NonTerm::props => Some(35),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        5 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        6 => match nt {
            NonTerm::prop_args(_) => Some(9),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        7 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        8 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        9 => match nt {
            NonTerm::code(_) => Some(10),
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
            NonTerm::code(_) => Some(18),
            NonTerm::rules => Some(15),
            NonTerm::rule => Some(17),
            NonTerm::section_second => Some(16),
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
            NonTerm::rule => Some(17),
            NonTerm::rules => Some(31),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        18 => match nt {
            NonTerm::rules => Some(30),
            NonTerm::rule => Some(17),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        19 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        20 => match nt {
            NonTerm::rule_right_idents(_) => Some(22),
            NonTerm::rule_rights(_) => Some(23),
            NonTerm::rule_right(_) => Some(21),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        21 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        22 => match nt {
            NonTerm::code(_) => Some(27),
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
            NonTerm::rule_right(_) => Some(26),
            NonTerm::rule_right_idents(_) => Some(22),
            NonTerm::S => None,
            _ => unreachable!(),
        },

        26 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        27 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        28 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        29 => match nt {
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
            NonTerm::code(_) => Some(34),
            NonTerm::section_third => Some(33),
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

        35 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        36 => match nt {
            NonTerm::S => None,
            _ => unreachable!(),
        },

        _ => unreachable!(),
    });

    while !parser.accepted() {
        match parser.state() {

0 => match parser.lookahead() {
Token::BRACKET_CODE(_) => parser.shift(7),
Token::PROP(_) => parser.shift(6),
Token::SECTION_SPLIT => parser.reduce(0, |right| {
let mut right = right;



return NonTerm::props;
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.shift(8),

    _ => parser.panic_location(filename, "Unexpected token")
},

1 => match parser.lookahead() {
Token::PROP(_) => parser.shift(6),
Token::SECTION_SPLIT => parser.reduce(0, |right| {
let mut right = right;



return NonTerm::props;
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

2 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::props) = right.pop().unwrap() {
let mut arg0 = ();

return NonTerm::section_first;
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

3 => match parser.lookahead() {
Token::END => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::doc) = right.pop().unwrap() {
let mut arg0 = ();

return NonTerm::S;
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

4 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(0, |right| {
let mut right = right;



return NonTerm::props;
unreachable!();
}),
Token::PROP(_) => parser.shift(6),

    _ => parser.panic_location(filename, "Unexpected token")
},

5 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.shift(14),

    _ => parser.panic_location(filename, "Unexpected token")
},

6 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::prop_args(Vec::new()); }
return NonTerm::prop_args(todo!("Implement for rule: prop_args ->"));
unreachable!();
}),
Token::PROP(_) => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::prop_args(Vec::new()); }
return NonTerm::prop_args(todo!("Implement for rule: prop_args ->"));
unreachable!();
}),
Token::ALIAS(_) => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::prop_args(Vec::new()); }
return NonTerm::prop_args(todo!("Implement for rule: prop_args ->"));
unreachable!();
}),
Token::LITERAL(_) => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::prop_args(Vec::new()); }
return NonTerm::prop_args(todo!("Implement for rule: prop_args ->"));
unreachable!();
}),
Token::IDENT(_) => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::prop_args(Vec::new()); }
return NonTerm::prop_args(todo!("Implement for rule: prop_args ->"));
unreachable!();
}),
Token::BRACKET_CODE(_) => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::prop_args(Vec::new()); }
return NonTerm::prop_args(todo!("Implement for rule: prop_args ->"));
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::prop_args(Vec::new()); }
return NonTerm::prop_args(todo!("Implement for rule: prop_args ->"));
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

7 => match parser.lookahead() {
Token::PROP(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> BRACKET_CODE"));
}
unreachable!();
}),
Token::BRACKET_CODE(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> BRACKET_CODE"));
}
unreachable!();
}),
Token::ALIAS(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> BRACKET_CODE"));
}
unreachable!();
}),
Token::RULE_DIV => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> BRACKET_CODE"));
}
unreachable!();
}),
Token::LITERAL(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> BRACKET_CODE"));
}
unreachable!();
}),
Token::IDENT(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> BRACKET_CODE"));
}
unreachable!();
}),
Token::SEMICOLON => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> BRACKET_CODE"));
}
unreachable!();
}),
Token::END => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> BRACKET_CODE"));
}
unreachable!();
}),
Token::SECTION_SPLIT => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> BRACKET_CODE"));
}
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::BRACKET_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> BRACKET_CODE"));
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

8 => match parser.lookahead() {
Token::BRACKET_CODE(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> PLAIN_CODE"));
}
unreachable!();
}),
Token::END => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> PLAIN_CODE"));
}
unreachable!();
}),
Token::PROP(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> PLAIN_CODE"));
}
unreachable!();
}),
Token::ALIAS(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> PLAIN_CODE"));
}
unreachable!();
}),
Token::SECTION_SPLIT => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> PLAIN_CODE"));
}
unreachable!();
}),
Token::LITERAL(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> PLAIN_CODE"));
}
unreachable!();
}),
Token::IDENT(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> PLAIN_CODE"));
}
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> PLAIN_CODE"));
}
unreachable!();
}),
Token::SEMICOLON => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> PLAIN_CODE"));
}
unreachable!();
}),
Token::RULE_DIV => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PLAIN_CODE(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::code(arg0); }
return NonTerm::code(todo!("Implement for rule: code -> PLAIN_CODE"));
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

9 => match parser.lookahead() {
Token::LITERAL(_) => parser.shift(11),
Token::PROP(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PROP(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{ builder.add_prop(arg0, arg1); }
return NonTerm::prop;
}
}
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.shift(8),
Token::ALIAS(_) => parser.shift(12),
Token::BRACKET_CODE(_) => parser.shift(7),
Token::SECTION_SPLIT => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::PROP(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{ builder.add_prop(arg0, arg1); }
return NonTerm::prop;
}
}
unreachable!();
}),
Token::IDENT(_) => parser.shift(13),

    _ => parser.panic_location(filename, "Unexpected token")
},

10 => match parser.lookahead() {
Token::ALIAS(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::code(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args code"));
}
}
unreachable!();
}),
Token::PROP(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::code(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args code"));
}
}
unreachable!();
}),
Token::SECTION_SPLIT => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::code(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args code"));
}
}
unreachable!();
}),
Token::IDENT(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::code(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args code"));
}
}
unreachable!();
}),
Token::BRACKET_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::code(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args code"));
}
}
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::code(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args code"));
}
}
unreachable!();
}),
Token::LITERAL(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::code(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args code"));
}
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

11 => match parser.lookahead() {
Token::ALIAS(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::LITERAL(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args LITERAL"));
}
}
unreachable!();
}),
Token::IDENT(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::LITERAL(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args LITERAL"));
}
}
unreachable!();
}),
Token::SECTION_SPLIT => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::LITERAL(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args LITERAL"));
}
}
unreachable!();
}),
Token::BRACKET_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::LITERAL(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args LITERAL"));
}
}
unreachable!();
}),
Token::PROP(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::LITERAL(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args LITERAL"));
}
}
unreachable!();
}),
Token::LITERAL(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::LITERAL(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args LITERAL"));
}
}
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::LITERAL(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args LITERAL"));
}
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

12 => match parser.lookahead() {
Token::BRACKET_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::ALIAS(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args ALIAS"));
}
}
unreachable!();
}),
Token::IDENT(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::ALIAS(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args ALIAS"));
}
}
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::ALIAS(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args ALIAS"));
}
}
unreachable!();
}),
Token::SECTION_SPLIT => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::ALIAS(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args ALIAS"));
}
}
unreachable!();
}),
Token::ALIAS(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::ALIAS(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args ALIAS"));
}
}
unreachable!();
}),
Token::PROP(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::ALIAS(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args ALIAS"));
}
}
unreachable!();
}),
Token::LITERAL(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::ALIAS(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args ALIAS"));
}
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

13 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args IDENT"));
}
}
unreachable!();
}),
Token::PROP(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args IDENT"));
}
}
unreachable!();
}),
Token::LITERAL(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args IDENT"));
}
}
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args IDENT"));
}
}
unreachable!();
}),
Token::ALIAS(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args IDENT"));
}
}
unreachable!();
}),
Token::IDENT(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args IDENT"));
}
}
unreachable!();
}),
Token::BRACKET_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop_args(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
	    	      arg0.push(arg1);
		      return NonTerm::prop_args(arg0);
	    }
return NonTerm::prop_args(todo!("Implement for rule: prop_args -> prop_args IDENT"));
}
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

14 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(0, |right| {
let mut right = right;



return NonTerm::rules;
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.shift(8),
Token::BRACKET_CODE(_) => parser.shift(7),
Token::IDENT(_) => parser.shift(19),

    _ => parser.panic_location(filename, "Unexpected token")
},

15 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rules) = right.pop().unwrap() {
let mut arg0 = ();

return NonTerm::section_second;
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

16 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.shift(32),

    _ => parser.panic_location(filename, "Unexpected token")
},

17 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(0, |right| {
let mut right = right;



return NonTerm::rules;
unreachable!();
}),
Token::IDENT(_) => parser.shift(19),

    _ => parser.panic_location(filename, "Unexpected token")
},

18 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(0, |right| {
let mut right = right;



return NonTerm::rules;
unreachable!();
}),
Token::IDENT(_) => parser.shift(19),

    _ => parser.panic_location(filename, "Unexpected token")
},

19 => match parser.lookahead() {
Token::COLON => parser.shift(20),

    _ => parser.panic_location(filename, "Unexpected token")
},

20 => match parser.lookahead() {
Token::PLAIN_CODE(_) => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::rule_right_idents(Vec::new()); }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents ->"));
unreachable!();
}),
Token::IDENT(_) => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::rule_right_idents(Vec::new()); }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents ->"));
unreachable!();
}),
Token::ALIAS(_) => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::rule_right_idents(Vec::new()); }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents ->"));
unreachable!();
}),
Token::BRACKET_CODE(_) => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::rule_right_idents(Vec::new()); }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents ->"));
unreachable!();
}),
Token::RULE_DIV => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::rule_right_idents(Vec::new()); }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents ->"));
unreachable!();
}),
Token::SEMICOLON => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::rule_right_idents(Vec::new()); }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents ->"));
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

21 => match parser.lookahead() {
Token::SEMICOLON => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_right(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::rule_rights(vec![arg0]); }
return NonTerm::rule_rights(todo!("Implement for rule: rule_rights -> rule_right"));
}
unreachable!();
}),
Token::RULE_DIV => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_right(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::rule_rights(vec![arg0]); }
return NonTerm::rule_rights(todo!("Implement for rule: rule_rights -> rule_right"));
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

22 => match parser.lookahead() {
Token::IDENT(_) => parser.shift(29),
Token::BRACKET_CODE(_) => parser.shift(7),
Token::RULE_DIV => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_right_idents(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::rule_right((arg0, None)); }
return NonTerm::rule_right(todo!("Implement for rule: rule_right -> rule_right_idents"));
}
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.shift(8),
Token::SEMICOLON => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_right_idents(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ return NonTerm::rule_right((arg0, None)); }
return NonTerm::rule_right(todo!("Implement for rule: rule_right -> rule_right_idents"));
}
unreachable!();
}),
Token::ALIAS(_) => parser.shift(28),

    _ => parser.panic_location(filename, "Unexpected token")
},

23 => match parser.lookahead() {
Token::SEMICOLON => parser.shift(24),
Token::RULE_DIV => parser.shift(25),

    _ => parser.panic_location(filename, "Unexpected token")
},

24 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(4, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::COLON) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::rule_rights(arg2)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::SEMICOLON) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = ();
let mut arg2 = arg2;
let mut arg3 = ();
{ builder.add_rule_with_eval(arg0, arg2); }
return NonTerm::rule;
}
}
}
}
unreachable!();
}),
Token::IDENT(_) => parser.reduce(4, |right| {
let mut right = right;



if let parser::StackElement::Token(Token::IDENT(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::COLON) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::rule_rights(arg2)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::SEMICOLON) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = ();
let mut arg2 = arg2;
let mut arg3 = ();
{ builder.add_rule_with_eval(arg0, arg2); }
return NonTerm::rule;
}
}
}
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

25 => match parser.lookahead() {
Token::RULE_DIV => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::rule_right_idents(Vec::new()); }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents ->"));
unreachable!();
}),
Token::BRACKET_CODE(_) => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::rule_right_idents(Vec::new()); }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents ->"));
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::rule_right_idents(Vec::new()); }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents ->"));
unreachable!();
}),
Token::IDENT(_) => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::rule_right_idents(Vec::new()); }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents ->"));
unreachable!();
}),
Token::SEMICOLON => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::rule_right_idents(Vec::new()); }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents ->"));
unreachable!();
}),
Token::ALIAS(_) => parser.reduce(0, |right| {
let mut right = right;


{ return NonTerm::rule_right_idents(Vec::new()); }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents ->"));
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

26 => match parser.lookahead() {
Token::SEMICOLON => parser.reduce(3, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_rights(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::RULE_DIV) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::rule_right(arg2)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = ();
let mut arg2 = arg2;
{
	      arg0.push(arg2);
	      return NonTerm::rule_rights(arg0);
	    }
return NonTerm::rule_rights(todo!("Implement for rule: rule_rights -> rule_rights RULE_DIV rule_right"));
}
}
}
unreachable!();
}),
Token::RULE_DIV => parser.reduce(3, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_rights(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::RULE_DIV) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::rule_right(arg2)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = ();
let mut arg2 = arg2;
{
	      arg0.push(arg2);
	      return NonTerm::rule_rights(arg0);
	    }
return NonTerm::rule_rights(todo!("Implement for rule: rule_rights -> rule_rights RULE_DIV rule_right"));
}
}
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

27 => match parser.lookahead() {
Token::SEMICOLON => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_right_idents(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::code(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{ return NonTerm::rule_right((arg0, Some(arg1))); }
return NonTerm::rule_right(todo!("Implement for rule: rule_right -> rule_right_idents code"));
}
}
unreachable!();
}),
Token::RULE_DIV => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_right_idents(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::code(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{ return NonTerm::rule_right((arg0, Some(arg1))); }
return NonTerm::rule_right(todo!("Implement for rule: rule_right -> rule_right_idents code"));
}
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

28 => match parser.lookahead() {
Token::RULE_DIV => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_right_idents(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::ALIAS(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
		    arg0.push(builder.get_alias(arg1));
		    return NonTerm::rule_right_idents(arg0);
		  }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents -> rule_right_idents ALIAS"));
}
}
unreachable!();
}),
Token::SEMICOLON => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_right_idents(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::ALIAS(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
		    arg0.push(builder.get_alias(arg1));
		    return NonTerm::rule_right_idents(arg0);
		  }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents -> rule_right_idents ALIAS"));
}
}
unreachable!();
}),
Token::ALIAS(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_right_idents(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::ALIAS(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
		    arg0.push(builder.get_alias(arg1));
		    return NonTerm::rule_right_idents(arg0);
		  }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents -> rule_right_idents ALIAS"));
}
}
unreachable!();
}),
Token::IDENT(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_right_idents(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::ALIAS(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
		    arg0.push(builder.get_alias(arg1));
		    return NonTerm::rule_right_idents(arg0);
		  }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents -> rule_right_idents ALIAS"));
}
}
unreachable!();
}),
Token::BRACKET_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_right_idents(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::ALIAS(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
		    arg0.push(builder.get_alias(arg1));
		    return NonTerm::rule_right_idents(arg0);
		  }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents -> rule_right_idents ALIAS"));
}
}
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_right_idents(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::ALIAS(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
		    arg0.push(builder.get_alias(arg1));
		    return NonTerm::rule_right_idents(arg0);
		  }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents -> rule_right_idents ALIAS"));
}
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

29 => match parser.lookahead() {
Token::RULE_DIV => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_right_idents(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
		    arg0.push(arg1);
		    return NonTerm::rule_right_idents(arg0);
		  }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents -> rule_right_idents IDENT"));
}
}
unreachable!();
}),
Token::BRACKET_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_right_idents(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
		    arg0.push(arg1);
		    return NonTerm::rule_right_idents(arg0);
		  }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents -> rule_right_idents IDENT"));
}
}
unreachable!();
}),
Token::PLAIN_CODE(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_right_idents(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
		    arg0.push(arg1);
		    return NonTerm::rule_right_idents(arg0);
		  }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents -> rule_right_idents IDENT"));
}
}
unreachable!();
}),
Token::IDENT(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_right_idents(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
		    arg0.push(arg1);
		    return NonTerm::rule_right_idents(arg0);
		  }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents -> rule_right_idents IDENT"));
}
}
unreachable!();
}),
Token::ALIAS(_) => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_right_idents(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
		    arg0.push(arg1);
		    return NonTerm::rule_right_idents(arg0);
		  }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents -> rule_right_idents IDENT"));
}
}
unreachable!();
}),
Token::SEMICOLON => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule_right_idents(arg0)) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::IDENT(arg1)) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = arg1;
{
		    arg0.push(arg1);
		    return NonTerm::rule_right_idents(arg0);
		  }
return NonTerm::rule_right_idents(todo!("Implement for rule: rule_right_idents -> rule_right_idents IDENT"));
}
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

30 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::code(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::rules) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = ();
{ builder.init_code(arg0); }
return NonTerm::section_second;
}
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

31 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::rule) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::rules) = right.pop().unwrap() {
let mut arg0 = ();
let mut arg1 = ();

return NonTerm::rules;
}
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

32 => match parser.lookahead() {
Token::BRACKET_CODE(_) => parser.shift(7),
Token::PLAIN_CODE(_) => parser.shift(8),
Token::END => parser.reduce(0, |right| {
let mut right = right;



return NonTerm::section_third;
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

33 => match parser.lookahead() {
Token::END => parser.reduce(5, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::section_first) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::SECTION_SPLIT) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::section_second) = right.pop().unwrap() {

if let parser::StackElement::Token(Token::SECTION_SPLIT) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::section_third) = right.pop().unwrap() {
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

    _ => parser.panic_location(filename, "Unexpected token")
},

34 => match parser.lookahead() {
Token::END => parser.reduce(1, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::code(arg0)) = right.pop().unwrap() {
let mut arg0 = arg0;
{ builder.fin_code(arg0); }
return NonTerm::section_third;
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

35 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::code(arg0)) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::props) = right.pop().unwrap() {
let mut arg0 = arg0;
let mut arg1 = ();
{ builder.header(arg0); }
return NonTerm::section_first;
}
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

36 => match parser.lookahead() {
Token::SECTION_SPLIT => parser.reduce(2, |right| {
let mut right = right;



if let parser::StackElement::NonTerminal(NonTerm::prop) = right.pop().unwrap() {

if let parser::StackElement::NonTerminal(NonTerm::props) = right.pop().unwrap() {
let mut arg0 = ();
let mut arg1 = ();

return NonTerm::props;
}
}
unreachable!();
}),

    _ => parser.panic_location(filename, "Unexpected token")
},

        _ => parser.panic_location(filename, "Unexpected token")
    }
    }

    return builder.build();
}
