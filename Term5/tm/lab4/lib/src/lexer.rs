use regex::Regex;

type F<T> = dyn Fn(String) -> T;

pub struct Lexer<T>
{
    lexems: Vec<Lexem<T>>,
}

#[derive(Debug)]
pub enum LexerError
{
    InvalidToken(usize),
}

impl<T> Lexer<T>
{
    pub fn new() -> Lexer<T> {
	Lexer {
	    lexems: Vec::<Lexem<T>>::new(),
	}
    }

    pub fn add<S: AsRef<str>, Fun: Fn(String) -> T + 'static>(&mut self, regex: S, token: Fun) {
	if let Ok(regex) = Regex::new(regex.as_ref()) {
	    self.lexems.push(Lexem::new(regex, token));
	} else {
	    panic!("Invalid regex: {}\nRegex are checked at generation step. This is mostly programmer's fault", regex.as_ref());
	}
    }

    pub fn lex<S: AsRef<str>>(self, input: S) -> Result<Vec<T>, LexerError> {
	let mut input: &str = input.as_ref();
	let mut res: Vec<T> = Vec::new();
	let mut pos: usize = 0;

	'input_read: while input.len() > 0 {
	    for lexem in self.lexems.iter() {
		if let Some((ninput, token)) = lexem.mtch(input) {
		    let pos_delta = input.len() - ninput.len();
		    assert!(pos_delta > 0, "Empty match");
		    input = ninput;
		    pos += pos_delta;
		    res.push(token);
		    continue 'input_read;
		}
	    }
	    return Err(LexerError::InvalidToken(pos + 1));
	}

	return Ok(res);
    }
}

pub struct Lexem<T> {
    regex: Regex,
    token: Box<F<T>>,
}

impl<T> Lexem<T> {
    pub fn new<Fun: Fn(String) -> T + 'static>(regex: Regex, token: Fun) -> Lexem<T> {
	Lexem {
	    regex,
	    token: Box::new(token),
	}
    }

    pub fn mtch<'a>(&self, input: &'a str) -> Option<(&'a str, T)> {
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
