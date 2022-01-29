use std::{fs::File, io::{BufReader, BufRead, Cursor}};

#[derive(Debug,PartialEq,Clone)]
pub enum Token {
    IDENTIFIER(String),
    LPAREN,
    RPAREN,
    COMMA,
    ASTERISK,
    SEMICOLON,
    END,
}

pub struct Tokenizer {
    source: Box<dyn BufRead>,
    position: usize,
    line: usize,
    line_position: usize,
    ch: Option<u8>,
    token: Option<Token>,

    filename: Option<String>,
}

impl Tokenizer {
    pub fn new(source: Box<dyn BufRead>) -> Tokenizer {
	let mut tokenizer = Tokenizer {
	    source,
	    ch: None,
	    token: None,
	    position: 0,
	    line: 0,
	    line_position: 0,

	    filename: None,
	};
	tokenizer.next_char();
	tokenizer
    }
    pub fn from_file(filename: String) -> Tokenizer {
	let mut tokenizer = Tokenizer::new(
	    Box::new(BufReader::new(File::open(&filename)
				    .expect(&format!("{}: could not open file for reading", &filename)))));
	tokenizer.filename = Some(filename);
	tokenizer
    }

    pub fn from_str(string: String) -> Tokenizer {
	Tokenizer::new(Box::new(Cursor::new(string.into_bytes())))
    }

    fn next_char(&mut self) {
	let mut c = [ 0u8 ];
	match self.source.as_mut().read(&mut c) {
	    Ok(1) => {
		self.ch = Some(c[0]);
		self.position += 1;
		if c[0] == b'\n' {
		    self.line += 1;
		    self.line_position = 0;
		}
	    },
	    Ok(0) => {
		self.ch = None;
	    },
	    Err(err) =>  {
		panic!("Could not read next character: {}", &err);
	    },
	    Ok(_) => {
		unreachable!();
	    }
	}
    }

    fn panic_location(&self, msg: &str) -> ! {
	if let Some(filename) = self.filename.as_ref() {
	    panic!("{}:{}:{}: ERROR: {}", filename, self.line, self.line_position, msg)
	} else {
	    panic!("{}: ERROR: {}", self.position, msg)
	}
    }

    fn read_while<P: Fn(usize, u8) -> bool>(&mut self, pred: P) -> Option<String> {
	let mut i = 0usize;
	let mut res = Vec::<u8>::new();
	while let Some(ch) = self.ch {
	    if pred(i, ch) {
		res.push(ch);
	    } else {
		break;
	    }
	    self.next_char();
	    i += 1;
	}
	if res.len() == 0 {
	    None
	} else {
	    Some(String::from_utf8(res)
		.expect("Invalid UTF-8 string in input"))
	}
    }

    pub fn cur_token(&self) -> Token {
	self.token.as_ref().unwrap().clone()
    }

    pub fn next_token(&mut self) {
	let identifer_pred = |i, ch: u8| {
	    if ch.is_ascii_alphanumeric() || ch == b'_' {
		!(i == 0 && ch.is_ascii_digit())
	    } else {
		false
	    }
	};

	let mut call_next = true;
	let res: Token = loop {
	    if let Some(ch) = self.ch {
		if ch.is_ascii_whitespace() {
		    self.next_char();
		    continue
		}
		break match ch {
		    b'(' => Token::LPAREN,
		    b')' => Token::RPAREN,
		    b'*' => Token::ASTERISK,
		    b',' => Token::COMMA,
		    b';' => Token::SEMICOLON,
		    _ => {
			if let Some(identifier) = self.read_while(identifer_pred) {
			    call_next = false;
			    Token::IDENTIFIER(identifier)
			} else {
			    self.panic_location("Unexpected token")
			}
		    }
		}
	    } else {
		break Token::END
	    }
	};
	if call_next {
	    self.next_char();
	}
	self.token = Some(res);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn tokenize(string: String) -> Vec<Token> {
	let mut res = Vec::new();
	let mut tokenizer = Tokenizer::from_str(string);
	tokenizer.next_token();

	loop {
	    let token = tokenizer.cur_token();
	    res.push(token.clone());
	    if token == Token::END {
		break;
	    }
	    tokenizer.next_token();
	}
	res
    }

    use Token::*;
    #[test]
    fn zero_args() {
	assert_eq!(tokenize("void test();".to_owned()),
		   vec![IDENTIFIER("void".to_owned()), IDENTIFIER("test".to_owned()),
			LPAREN, RPAREN,
			SEMICOLON, END]);
    }

    #[test]
    fn one_arg() {
	assert_eq!(tokenize("void test(int a);".to_owned()),
		   vec![IDENTIFIER("void".to_owned()), IDENTIFIER("test".to_owned()),
			LPAREN, IDENTIFIER("int".to_owned()), IDENTIFIER("a".to_owned()), RPAREN,
			SEMICOLON, END]);
    }

    #[test]
    fn one_ptr_arg() {
	assert_eq!(tokenize("void test(int *a);".to_owned()),
		   vec![IDENTIFIER("void".to_owned()), IDENTIFIER("test".to_owned()),
			LPAREN, IDENTIFIER("int".to_owned()), ASTERISK, IDENTIFIER("a".to_owned()), RPAREN,
			SEMICOLON, END]);
    }

    #[test]
    fn multi_args() {
	assert_eq!(tokenize("void test(int a, float b);".to_owned()),
		   vec![IDENTIFIER("void".to_owned()), IDENTIFIER("test".to_owned()),
			LPAREN, IDENTIFIER("int".to_owned()), IDENTIFIER("a".to_owned()), COMMA,
			IDENTIFIER("float".to_owned()), IDENTIFIER("b".to_owned()), RPAREN,
			SEMICOLON, END]);
    }

    #[test]
    fn multi_ptr_args() {
	assert_eq!(tokenize("void test(int* a, float * * b);".to_owned()),
		   vec![IDENTIFIER("void".to_owned()), IDENTIFIER("test".to_owned()),
			LPAREN, IDENTIFIER("int".to_owned()), ASTERISK, IDENTIFIER("a".to_owned()), COMMA,
			IDENTIFIER("float".to_owned()), ASTERISK, ASTERISK, IDENTIFIER("b".to_owned()), RPAREN,
			SEMICOLON, END]);
    }

    #[test]
    fn valid_identifier_with_numbers() {
	tokenize("void te32s3t(int arg);".to_owned());
    }

    #[should_panic]
    #[test]
    fn invalid_identifier() {
	tokenize("void 2test(int arg);".to_owned());
    }

    #[should_panic]
    #[test]
    fn invalid_token() {
	tokenize("void test(int &arg);".to_owned());
    }
}
