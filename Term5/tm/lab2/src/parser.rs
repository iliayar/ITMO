use std::io::BufRead;

use super::tokenizer::*;

#[derive(Debug,PartialEq,Clone)]
pub enum NodeValue {
    NonTerminal(String),
    Terminal(Token),
}

#[derive(Debug,PartialEq,Clone)]
pub struct Tree {
    pub value: NodeValue,
    pub childs: Vec<Tree>,
}

impl Tree {
    fn new(value: NodeValue, childs: Vec<Tree>) -> Tree {
	Tree { value, childs }
    }
    fn node(value: NodeValue) -> Tree {
	Tree::new(value, vec![])
    }
}

pub struct Parser {
    tokenizer: Option<Tokenizer>,
}

impl Parser {
    pub fn new() -> Parser {
	Parser {
	    tokenizer: None,
	}
    }

    fn parse_tokenizer(&mut self, tokenizer: Tokenizer) -> Tree {
	self.tokenizer = Some(tokenizer);
	self.parse_impl()
    }

    pub fn parse(&mut self, source: Box<dyn BufRead>) -> Tree {
	self.parse_tokenizer(Tokenizer::new(source))
    }

    pub fn parse_str(&mut self, string: String) -> Tree {
	self.parse_tokenizer(Tokenizer::from_str(string))
    }

    pub fn parse_file(&mut self, filename: String) -> Tree {
	self.parse_tokenizer(Tokenizer::from_file(filename))
    }

    fn tkn(&mut self) -> &mut Tokenizer {
	self.tokenizer.as_mut()
	    .expect("Tokinzer is None. Should not happen")
    }

    fn parse_impl(&mut self) -> Tree {
	self.tkn().next_token();
	self.DECLARATION()
    }

    #[allow(non_snake_case)]
    fn DECLARATION(&mut self) -> Tree {
	match self.tkn().cur_token() {
	    t @ Token::IDENTIFIER(_) => {
		// IDENTIFIER
		self.tkn().next_token();

		// IDENTIFIER
		let name = self.tkn().cur_token();
		assert!(matches!(name, Token::IDENTIFIER(_)));
		self.tkn().next_token();

		// (
		assert!(matches!(self.tkn().cur_token(), Token::LPAREN));
		self.tkn().next_token();

		// ARGS
		let args = self.ARGS();

		// )
		assert!(matches!(self.tkn().cur_token(), Token::RPAREN));
		self.tkn().next_token();

		// ;
		assert!(matches!(self.tkn().cur_token(), Token::SEMICOLON));
		self.tkn().next_token();

		// $
		assert!(matches!(self.tkn().cur_token(), Token::END));

		Tree::new(NodeValue::NonTerminal("DECLARATION".to_owned()), vec![
		    Tree::node(NodeValue::Terminal(t)),
		    Tree::node(NodeValue::Terminal(name)),
		    Tree::node(NodeValue::Terminal(Token::LPAREN)),
		    args,
		    Tree::node(NodeValue::Terminal(Token::RPAREN)),
		    Tree::node(NodeValue::Terminal(Token::SEMICOLON)),
		])
	    },
	    t => panic!("Unexpected token: {:?}", t)
	}
    }

    #[allow(non_snake_case)]
    fn ARGS(&mut self) -> Tree {
	match self.tkn().cur_token() {
	    Token::IDENTIFIER(_) => {

		// ARG
		let arg = self.ARG();

		// ARGS_REST
		let args_rest = self.ARGS_REST();

		Tree::new(NodeValue::NonTerminal("ARGS".to_owned()), vec![
		    arg,
		    args_rest
		])
	    },
	    Token::RPAREN => {
		Tree::node(NodeValue::NonTerminal("ARGS".to_owned()))
	    },
	    t => panic!("Unexpected token: {:?}", t)
	}
    }

    #[allow(non_snake_case)]
    fn ARGS_REST(&mut self) -> Tree {
	match self.tkn().cur_token() {
	    Token::COMMA => {
		// ,
		self.tkn().next_token();

		// ARG
		let arg = self.ARG();

		// ARGS_REST
		let args_rest = self.ARGS_REST();

		Tree::new(NodeValue::NonTerminal("ARGS_REST".to_owned()), vec![
		    Tree::node(NodeValue::Terminal(Token::COMMA)),
		    arg,
		    args_rest
		])
	    },
	    Token::RPAREN => {
		Tree::node(NodeValue::NonTerminal("ARGS_REST".to_owned()))
	    }
	    t => panic!("Unexpected token: {:?}", t)
	}
    }

    #[allow(non_snake_case)]
    fn ARG(&mut self) -> Tree {
	match self.tkn().cur_token() {
	    t @ Token::IDENTIFIER(_) => {
		// IDENTIFIER
		self.tkn().next_token();

		// POINTER
		let pointer = self.POINTER();

		// IDENTIFIER
		let name = self.tkn().cur_token();
		assert!(matches!(name, Token::IDENTIFIER(_)));
		self.tkn().next_token();

		Tree::new(NodeValue::NonTerminal("ARG".to_owned()), vec![
		    Tree::node(NodeValue::Terminal(t)),
		    pointer,
		    Tree::node(NodeValue::Terminal(name))
		])
	    },
	    t => panic!("Unexpected token: {:?}", t)
	}
    }

    #[allow(non_snake_case)]
    fn POINTER(&mut self) -> Tree {
	match self.tkn().cur_token() {
	    Token::ASTERISK => {
		// *
		self.tkn().next_token();

		// POINTER
		let pointer = self.POINTER();

		Tree::new(NodeValue::NonTerminal("POINTER".to_owned()), vec![
		    Tree::node(NodeValue::Terminal(Token::ASTERISK)),
		    pointer
		])
	    },
	    Token::IDENTIFIER(_) => {
		Tree::node(NodeValue::NonTerminal("POINTER".to_owned()))
	    },
	    t => panic!("Unexpected token: {:?}", t)
	}
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    // Tests for inner functions

    fn parse_tree_with<M: Fn(&mut Parser) -> Tree>(string: String, method: M) -> Tree {
	let mut parser = Parser::new();
	parser.tokenizer = Some(Tokenizer::from_str(string));
	parser.tkn().next_token();
	method(&mut parser)
    }

    fn pointers_tree(n: usize) -> Tree {
	Tree::new(NodeValue::NonTerminal("POINTER".to_owned()), if n == 0 {
	    vec![]
	} else {
	    vec![
		Tree::node(NodeValue::Terminal(Token::ASTERISK)),
		pointers_tree(n - 1)
	    ]
	})
    }

    // POINTERS Rule. Tests for different count of asterisks. It
    // should be followed by argument name.

    #[test]
    fn pointers_zero() {
	assert_eq!(parse_tree_with("arg".to_owned(), Parser::POINTER), pointers_tree(0))
    }

    #[test]
    fn pointers_one() {
	assert_eq!(parse_tree_with("* arg".to_owned(), Parser::POINTER), pointers_tree(1))
    }

    #[test]
    fn pointers_many() {
	assert_eq!(parse_tree_with("* ** * arg".to_owned(), Parser::POINTER), pointers_tree(4))
    }

    // ARG Rule. Tests for argument declaration with zero or more
    // astersisks. Must not be empty.

    fn arg(t: String, pointers: usize, name: String) -> Tree {
	Tree::new(NodeValue::NonTerminal("ARG".to_owned()), vec![
	    Tree::node(NodeValue::Terminal(Token::IDENTIFIER(t))),
	    pointers_tree(pointers),
	    Tree::node(NodeValue::Terminal(Token::IDENTIFIER(name))),
	])
    }

    #[test]
    fn simple_arg() {
	assert_eq!(parse_tree_with("int a".to_owned(), Parser::ARG), arg("int".to_owned(), 0, "a".to_owned()))
    }

    #[test]
    fn simple_arg_with_pointers() {
	assert_eq!(parse_tree_with("int* *a".to_owned(), Parser::ARG), arg("int".to_owned(), 2, "a".to_owned()))
    }

    // ARGS Rule. Test for zero of more arguemnts with the variants
    // similar to prev test.

    fn args_tree(args: Vec<Tree>) -> Tree {
	if args.len() == 0 {
	    return Tree::new(NodeValue::NonTerminal("ARGS".to_owned()), vec![]);
	}

	let mut res = Tree::new(NodeValue::NonTerminal("ARGS_REST".to_owned()), vec![]);
	for i in (1..args.len()).rev() {
	    res = Tree::new(NodeValue::NonTerminal("ARGS_REST".to_owned()), vec![
		Tree::node(NodeValue::Terminal(Token::COMMA)),
		args[i].clone(),
		res,
	    ]);
	}

	Tree::new(NodeValue::NonTerminal("ARGS".to_owned()), vec![
	    args[0].clone(),
	    res
	])
    }

    #[test]
    fn zero_args() {
	assert_eq!(parse_tree_with(")".to_owned(), Parser::ARGS), args_tree(vec![]))
    }

    #[test]
    fn one_arg() {
	assert_eq!(parse_tree_with("int a)".to_owned(), Parser::ARGS), args_tree(vec![
	    arg("int".to_owned(), 0, "a".to_owned()),
	]))
    }

    #[test]
    fn multi_args() {
	assert_eq!(parse_tree_with("int a, float b)".to_owned(), Parser::ARGS), args_tree(vec![
	    arg("int".to_owned(), 0, "a".to_owned()),
	    arg("float".to_owned(), 0, "b".to_owned()),
	]))
    }

    #[test]
    fn multi_args_with_pointers() {
	assert_eq!(parse_tree_with("int* *a, float ** *b)".to_owned(), Parser::ARGS), args_tree(vec![
	    arg("int".to_owned(), 2, "a".to_owned()),
	    arg("float".to_owned(), 3, "b".to_owned()),
	]))
    }


    // Test for public interface

    fn fun_with_args(t: String, name: String, args: Vec<Tree>) -> Tree {
	Tree::new(NodeValue::NonTerminal("DECLARATION".to_owned()), vec![
	    Tree::node(NodeValue::Terminal(Token::IDENTIFIER(t))),
	    Tree::node(NodeValue::Terminal(Token::IDENTIFIER(name))),
	    Tree::node(NodeValue::Terminal(Token::LPAREN)),
	    args_tree(args),
	    Tree::node(NodeValue::Terminal(Token::RPAREN)),
	    Tree::node(NodeValue::Terminal(Token::SEMICOLON)),
	])
    }

    fn parse_tree(string: String) -> Tree {
	let mut parser = Parser::new();
	parser.parse_str(string)
    }

    #[test]
    fn empty_args() {
	assert_eq!(parse_tree("void fn();".to_owned()), fun_with_args("void".to_owned(), "fn".to_owned(), vec![]))
    }

    #[test]
    fn one_arg_fun() {
	assert_eq!(parse_tree("void fn(int a);".to_owned()), fun_with_args("void".to_owned(), "fn".to_owned(), vec![
	    arg("int".to_owned(), 0, "a".to_owned()),
	]))
    }

    #[test]
    fn multi_args_fun() {
	assert_eq!(parse_tree("void fn(int a, float b);".to_owned()), fun_with_args("void".to_owned(), "fn".to_owned(), vec![
	    arg("int".to_owned(), 0, "a".to_owned()),
	    arg("float".to_owned(), 0, "b".to_owned()),
	]))
    }

    #[test]
    fn multi_pointer_args_fun() {
	assert_eq!(parse_tree("void fn(int* a, float * *b);".to_owned()), fun_with_args("void".to_owned(), "fn".to_owned(), vec![
	    arg("int".to_owned(), 1, "a".to_owned()),
	    arg("float".to_owned(), 2, "b".to_owned()),
	]))
    }

    // Tests for invalid declaration

    #[should_panic]
    #[test]
    fn no_semicolon_zero_args() {
	parse_tree("void fn()".to_owned());
    }

    #[should_panic]
    #[test]
    fn no_semicolon_one_arg() {
	parse_tree("void fn(int a)".to_owned());
    }
    #[should_panic]
    #[test]
    fn no_semicolon_multi_args_ptr() {
	parse_tree("void fn(int *a, float * * b)".to_owned());
    }

    #[should_panic]
    #[test]
    fn no_type_or_function_name() {
	parse_tree("fn();".to_owned());
    }

    #[should_panic]
    #[test]
    fn no_parenthesis() {
	parse_tree("int a;".to_owned());
    }
}
