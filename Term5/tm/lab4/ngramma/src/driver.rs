
pub mod lexer {
    #[derive(Debug)]
    pub struct Token {
	pub regex: String,
	pub expr: String,
    }

    impl Token {
	pub fn new(regex: String, expr: String) -> Self { Self { regex, expr } }
    }

    #[derive(Debug)]
    pub struct Lex {
	pub tokens: Vec<Token>,
	pub end: String,
    }

    pub struct LexBuilder {
	tokens: Vec<Token>,
	end: Option<String>,
    }

    impl LexBuilder {
	pub fn new() -> LexBuilder {
	    LexBuilder {
		tokens: Vec::new(),
		end: None,
	    }
	}

	pub fn add_token(&mut self, t: Token) -> &mut LexBuilder {
	    self.tokens.push(t);
	    return self;
	}

	pub fn end(&mut self, s: String) -> &mut LexBuilder {
	    self.end = Some(s);
	    return self;
	}

	pub fn build(self) -> Lex {
	    Lex {
		tokens: self.tokens,
		end: self.end.unwrap(),
	    }
	}
    }
}
