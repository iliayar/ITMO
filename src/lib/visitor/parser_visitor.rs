use crate::token;
use crate::Token;
use crate::TokenVisitor;

use super::match_visitor::{match_token, Matched};

use thiserror::Error;

#[derive(Error, Debug)]
pub enum ParserError {
    #[error("Unexpected close brace")]
    UnexpectedCloseBrace,
    #[error("Trying pop from empty stack")]
    PopFromEmptyStack,
}

type Tokens = Vec<Box<dyn Token>>;

struct ParserVisitor {
    res: Tokens,
    stack: Tokens,
    brace_balance: usize,
    err: Option<ParserError>,
}

impl ParserVisitor {
    fn new() -> Self {
        ParserVisitor {
            res: Tokens::new(),
            stack: Tokens::new(),
            brace_balance: 0,
            err: None,
        }
    }

    fn dec_balance(&mut self) {
        if self.brace_balance == 0 {
            self.err = Some(ParserError::UnexpectedCloseBrace);
            return;
        }

        self.brace_balance -= 1;
    }

    fn inc_balance(&mut self) {
        self.brace_balance += 1;
    }

    fn is_error(&self) -> bool {
        self.err.is_some()
    }

    fn set_error(&mut self, error: ParserError) {
        self.err = Some(error);
    }

    fn move_from_stack(&mut self) {
        if let Some(token) = self.stack.pop() {
            self.res.push(token);
        } else {
            self.set_error(ParserError::PopFromEmptyStack);
        }
    }

    fn match_top(&self) -> Matched {
        if let Some(token) = self.stack.last() {
            match_token(token.as_ref())
        } else {
            Matched::None
        }
    }

    fn get_tokens(mut self) -> Result<Tokens, ParserError> {
        while !self.stack.is_empty() {
            self.move_from_stack();
        }

        if let Some(err) = self.err {
            Err(err)
        } else {
            Ok(self.res)
        }
    }
}

impl TokenVisitor for ParserVisitor {
    fn visit_operation(&mut self, token: &token::Operation) {
        if self.is_error() {
            return;
        }

        let prior = match match_token(token) {
            Matched::Operator { prior, .. } => prior,
            matched => panic!("Matched operation: {:?}", matched),
        };

        loop {
            if self.is_error() {
                return;
            }

            match self.match_top() {
                Matched::Operator {
                    prior: top_prior,
                    assoc,
                } => {
                    if prior >= top_prior {
                        self.move_from_stack();
			continue;
                    } else {
                        self.stack.push(Box::new(*token));
                    }
                }
                Matched::OpenBrace | Matched::None => {
                    self.stack.push(Box::new(*token));
                }
                matched => panic!("Matched on top of the stack: {:?}", matched),
            }

	    return;
        }
    }

    fn visit_brace(&mut self, token: &token::Brace) {
        if self.is_error() {
            return;
        }

        match token {
            token::Brace::LEFT => {
                self.stack.push(Box::new(*token));
                self.inc_balance()
            }
            token::Brace::RIGHT => loop {
                if self.is_error() {
                    return;
                }

                match self.match_top() {
                    Matched::OpenBrace => {
                        self.stack.pop();
                        self.dec_balance();
                        return;
                    }
                    _ => {
                        self.move_from_stack();
                    }
                };
            },
        }
    }

    fn visit_number(&mut self, token: &token::NumberToken) {
        if self.is_error() {
            return;
        }

        self.res.push(Box::new(*token));
    }
}

pub fn parse(tokens: Tokens) -> Result<Tokens, ParserError> {
    let mut visitor = ParserVisitor::new();
    for token in tokens {
        token.accept(&mut visitor);
    }

    visitor.get_tokens()
}
