use regex::Regex;

type F<T> = dyn Fn(String) -> T;

pub struct Lexer<T>
{
    lexems: Vec<Lexem<Box<F<T>>>>,
}

impl<T> Lexer<T>
{
    pub fn new() -> Lexer<T> {
	Lexer {
	    lexems: Vec::<Lexem<Box<F<T>>>>::new(),
	}
    }

    pub fn add<S: AsRef<str>, Fun: Fn(String) -> T + 'static>(&mut self, regex: S, token: Fun) -> Option<()> {
	if let Ok(regex) = Regex::new(regex.as_ref()) {
	    self.lexems.push(Lexem::new(regex, Box::new(token)));
	    return Some(());
	} else {
	    return None;
	}
    }

    pub fn lex<S: AsRef<str>>(self, input: S) -> Vec<T> {
	let mut input: &str = input.as_ref();
	let mut res: Vec<T> = Vec::new();
	let mut position: usize = 0;

	'input_read: while input.len() > 0 {
	    for lexem in self.lexems.iter() {
		if let Some(mtch) = lexem.regex.find(input) {
		    if mtch.start() == 0 {
			input = &input[mtch.end()..];
			res.push((lexem.token)(mtch.as_str().to_string()));
			position += mtch.end();
			continue 'input_read;
		    }
		}
	    }
	    panic!("Unknown token at position: {}", position);
	}

	return res;
    }
}

pub struct Lexem<T> {
    regex: Regex,
    token: T,
}

impl<T> Lexem<T> {
    pub fn new(regex: Regex, token: T) -> Lexem<T> {
	Lexem {
	    regex,
	    token,
	}
    }
}
