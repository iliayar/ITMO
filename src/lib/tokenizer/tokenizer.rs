use crate::token;
use crate::Token;
use thiserror::Error;

use log::*;

#[derive(Error, Debug)]
pub enum TokenizerError {
    #[error("Trying get tokens from non terminal state")]
    NotEnd,
    #[error("Unknown token: {0}")]
    UnknownToken(char),
    #[error("Invalid numeric token: {0}")]
    InvalidInt(#[from] std::num::ParseIntError),
}

type Tokens = Vec<Box<dyn Token>>;

trait State<'a> {
    fn advance(self: Box<Self>) -> Box<dyn State<'a> + 'a>;
    fn is_eof(&self) -> bool;
    fn get_tokens(self: Box<Self>) -> Result<Tokens, TokenizerError>;
}

pub fn tokenize<S: AsRef<str>>(input: S) -> Result<Tokens, TokenizerError> {
    let mut state = state::start(input.as_ref());

    while !state.is_eof() {
        state = state.advance();
    }

    state.get_tokens()
}

mod state {

    use log::debug;

    use super::{token, State, Token, TokenizerError, Tokens};

    struct Source<'a> {
        chars: std::str::Chars<'a>,
        cur: Option<char>,
    }

    impl<'a> Source<'a> {
        fn from_str(s: &'a str) -> Self {
            let mut chars = s.chars();
            let cur = chars.next();

            Self { chars, cur }
        }

        fn next(&mut self) {
            self.cur = self.chars.next();
        }

        fn cur(&self) -> Option<char> {
            self.cur
        }
    }

    struct StateHelper<'a> {
        src: Source<'a>,
        out: Tokens,
    }

    impl<'a> StateHelper<'a> {
        fn new(s: &'a str) -> Self {
            Self {
                src: Source::from_str(s),
                out: Vec::new(),
            }
        }

        fn cur(&self) -> Option<char> {
            self.src.cur()
        }

        fn next(&mut self) {
            self.src.next();
        }

        fn add(&mut self, token: impl Token + 'static) {
            self.out.push(Box::new(token));
        }

        fn get_tokens(self) -> Tokens {
            self.out
        }

        fn advancing(mut self) -> Self {
            self.next();
            self
        }

        fn with_token(mut self, token: impl Token + 'static) -> Self {
            self.add(token);
            self
        }
    }

    pub fn start<'a>(input: &'a str) -> Box<dyn State<'a> + 'a> {
        let helper = StateHelper::new(input);
        Start::new(helper)
    }

    struct Start<'a> {
        helper: StateHelper<'a>,
    }

    struct Number<'a> {
        helper: StateHelper<'a>,
        str_number: String,
    }

    struct End<'a> {
        helper: StateHelper<'a>,
    }

    struct Error {
        err: TokenizerError,
    }

    impl<'a> Start<'a> {
        fn new(helper: StateHelper<'a>) -> Box<dyn State<'a> + 'a> {
            Box::new(Start { helper })
        }

        fn with_token(self: Box<Self>, token: impl Token + 'static) -> Box<dyn State<'a> + 'a> {
            Start::new(self.helper.advancing().with_token(token))
        }
    }

    impl<'a> State<'a> for Start<'a> {
        fn advance(self: Box<Self>) -> Box<dyn State<'a> + 'a> {
            if let Some(chr) = self.helper.cur() {
                if chr.is_whitespace() {
                    Start::new(self.helper.advancing())
                } else if chr.is_numeric() {
                    Number::new(self.helper, String::new())
                } else {
                    match chr {
                        '+' => self.with_token(token::Operation::ADD),
                        '-' => self.with_token(token::Operation::SUB),
                        '*' => self.with_token(token::Operation::MUL),
                        '/' => self.with_token(token::Operation::DIV),
                        '(' => self.with_token(token::Brace::LEFT),
                        ')' => self.with_token(token::Brace::RIGHT),
                        _ => Error::new(TokenizerError::UnknownToken(chr)),
                    }
                }
            } else {
                End::new(self.helper)
            }
        }

        fn is_eof(&self) -> bool {
            false
        }

        fn get_tokens(self: Box<Self>) -> Result<Tokens, TokenizerError> {
            Err(TokenizerError::NotEnd)
        }
    }

    impl<'a> Number<'a> {
        fn new(helper: StateHelper<'a>, str_number: String) -> Box<dyn State<'a> + 'a> {
            Box::new(Number { helper, str_number })
        }
    }

    impl<'a> State<'a> for Number<'a> {
        fn advance(mut self: Box<Self>) -> Box<dyn State<'a> + 'a> {
            if let Some(chr) = self.helper.cur() {
                if chr.is_numeric() {
                    self.str_number.push(chr);
                    return Number::new(self.helper.advancing(), self.str_number);
                }
            }

            match self.str_number.parse::<i64>() {
                Ok(value) => Start::new(self.helper.with_token(token::NumberToken { value })),
                Err(err) => Error::new(err.into()),
            }
        }

        fn is_eof(&self) -> bool {
            false
        }

        fn get_tokens(self: Box<Self>) -> Result<Tokens, TokenizerError> {
            Err(TokenizerError::NotEnd)
        }
    }

    impl<'a> End<'a> {
        fn new(helper: StateHelper<'a>) -> Box<dyn State + 'a> {
            Box::new(End { helper })
        }
    }

    impl<'a> State<'a> for End<'a> {
        fn advance(self: Box<Self>) -> Box<dyn State<'a> + 'a> {
            End::new(self.helper)
        }

        fn is_eof(&self) -> bool {
            true
        }

        fn get_tokens(self: Box<Self>) -> Result<super::Tokens, TokenizerError> {
            Ok(self.helper.get_tokens())
        }
    }

    impl<'a> Error {
        fn new(err: TokenizerError) -> Box<dyn State<'a> + 'a> {
            Box::new(Error { err })
        }
    }

    impl<'a> State<'a> for Error {
        fn advance(self: Box<Self>) -> Box<dyn State<'a> + 'a> {
            Error::new(self.err)
        }

        fn is_eof(&self) -> bool {
            true
        }

        fn get_tokens(self: Box<Self>) -> Result<super::Tokens, TokenizerError> {
            Err(self.err)
        }
    }
}
