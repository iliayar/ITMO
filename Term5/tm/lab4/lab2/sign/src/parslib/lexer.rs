

use std::{io::BufRead, collections::VecDeque};

use fancy_regex::Regex;

pub struct Token<T> {
    pub token: T,
    pub pos: (usize, usize),
}

impl<T> Token<T> {
    pub fn new(token: T, pos: (usize, usize)) -> Self { Self { token, pos } }
}

pub struct Lexer<T>
{
    lexems: Vec<Lexem<T>>,
    end: T,
}

#[derive(Debug)]
pub enum LexerError
{
    InvalidToken(usize),
}

pub struct StreamLexer<'a, R: BufRead, T, FE: Fn(LexerError, String) -> ()> {
    source: &'a mut R,
    lexems: Vec<Lexem<T>>,
    end: Option<T>,
    pub buf: VecDeque<Token<T>>,
    pos: usize,
    onerror: FE,
    pub all_input: Option<String>,
}

impl<'a, R: BufRead, T, FE: Fn(LexerError, String) -> ()> StreamLexer<'a, R, T, FE> {

    pub fn fill(&mut self) {
	if self.buf.len() > 0 || self.end.is_none() {
	    return;
	}

	let mut input = String::new();
	let res =  self.source.read_line(&mut input);

	if let Ok(n) = res {
	    if n == 0 {
		self.buf.push_back(Token::new(self.end.take().unwrap(), (self.pos, self.pos)));
		return;
	    }
	} else if let Err(e) = res {
	    panic!("Failed to read input: {}", e);
	}

	self.all_input.as_mut().unwrap().push_str(&input);

	let mut input: &str = input.as_ref();

	'input_read: while input.len() > 0 {
	    for lexem in self.lexems.iter() {
		if let Some((ninput, token)) = lexem.mtch(input) {
		    let pos_delta = input.len() - ninput.len();
		    assert!(pos_delta > 0, "Empty match");
		    input = ninput;
		    if let Some(token) = token {
			self.buf.push_back(Token::new(token, (self.pos, self.pos + pos_delta)));
		    }
		    self.pos += pos_delta;
		    continue 'input_read;
		}
	    }
	    (self.onerror)(LexerError::InvalidToken(self.pos + 1), self.all_input.take().unwrap());
	}
    }
}

impl<T> Lexer<T>
{
    pub fn new(end: T) -> Lexer<T> {
	Lexer {
	    lexems: Vec::<Lexem<T>>::new(),
	    end,
	}
    }

    pub fn add<S: AsRef<str>, Fun: Fn(String) -> Option<T> + 'static>(&mut self, regex: S, token: Fun) {
	if let Ok(regex) = Regex::new(regex.as_ref()) {
	    self.lexems.push(Lexem::new(regex, token));
	} else {
	    panic!("Invalid regex: {}\nRegex are checked at generation step. This is mostly programmer's fault", regex.as_ref());
	}
    }

    pub fn lex_stream<'a, R: BufRead, FE: Fn(LexerError, String) -> ()>(self, source: &'a mut R, onerror: FE) -> StreamLexer<'a, R, T, FE> {
	StreamLexer {
	    source,
	    lexems: self.lexems,
	    end: Some(self.end),
	    buf: VecDeque::new(),
	    pos: 0,
	    onerror,
	    all_input: Some(String::new()),
	}
    }

    pub fn lex<S: AsRef<str>>(self, sinput: S) -> Result<(Vec<Token<T>>, S), LexerError> {
	let mut input: &str = sinput.as_ref();
	let mut res: Vec<Token<T>> = Vec::new();
	let mut pos: usize = 0;

	'input_read: while input.len() > 0 {
	    for lexem in self.lexems.iter() {
		if let Some((ninput, token)) = lexem.mtch(input) {
		    let pos_delta = input.len() - ninput.len();
		    assert!(pos_delta > 0, "Empty match");
		    input = ninput;
		    if let Some(token) = token {
			res.push(Token::new(token, (pos, pos + pos_delta)));
		    }
		    pos += pos_delta;
		    continue 'input_read;
		}
	    }
	    return Err(LexerError::InvalidToken(pos + 1));
	}

	res.push(Token::new(self.end, (pos, pos)));
	return Ok((res, sinput));
    }
}

pub struct Lexem<T> {
    regex: Regex,
    token: Box<dyn Fn(String) -> Option<T>>,
}

impl<T> Lexem<T> {
    pub fn new<Fun: Fn(String) -> Option<T> + 'static>(regex: Regex, token: Fun) -> Lexem<T> {
	Lexem {
	    regex,
	    token: Box::new(token),
	}
    }

    pub fn mtch<'a>(&self, input: &'a str) -> Option<(&'a str, Option<T>)> {
	if let Ok(Some(mtch)) = self.regex.find(input) {
	    if mtch.start() == 0 {
		Some((
		    &input[mtch.end()..],
		    (self.token)(mtch.as_str().to_string()),
		))
	    } else {
		None
	    }
	} else {
	    None
	}
    }
}
