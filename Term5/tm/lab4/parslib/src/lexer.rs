use regex::Regex;

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

    pub fn lex<S: AsRef<str>>(self, input: S) -> Result<Vec<Token<T>>, LexerError> {
	let mut input: &str = input.as_ref();
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
	return Ok(res);
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
	if let Some(mtch) = self.regex.find(input) {
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
