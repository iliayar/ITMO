use crate::token;
use crate::Token;
use crate::TokenVisitor;

use thiserror::Error;

use log::*;

use super::visitor;

#[derive(Error, Debug)]
pub enum EvalError {
    #[error("Expression not in rpn")]
    NonRPNExpression,
    #[error("Invalid arity for operation {0}")]
    InvalidArity(String),
    #[error("Division by zero occured")]
    DivByZero,
    #[error("No operands on the stack")]
    NotEnoughOperands,
    #[error("Too many operands on the stack")]
    TooManyOperands,
}

struct EvalVisitor {
    stack: Vec<i64>,
    err: Option<EvalError>,
}

impl EvalVisitor {
    fn new() -> Self {
        Self {
            stack: Vec::new(),
            err: None,
        }
    }

    fn set_error(&mut self, err: EvalError) {
        self.err = Some(err);
    }

    fn is_error(&self) -> bool {
        self.err.is_some()
    }

    fn apply_stack(
        &mut self,
        op_notaion: String,
        operation: impl Fn(i64, i64) -> Result<i64, EvalError>,
    ) {
        if let Some(op_right) = self.stack.pop() {
            if let Some(op_left) = self.stack.pop() {
                match operation(op_left, op_right) {
                    Ok(res) => {
                        self.stack.push(res);
                    }
                    Err(err) => {
                        self.set_error(err);
                    }
                }
		return;
            }
        }

        self.set_error(EvalError::InvalidArity(op_notaion));
    }

    fn get_result(mut self) -> Result<i64, EvalError> {
        if let Some(err) = self.err {
            Err(err)
        } else if self.stack.len() < 1 {
            Err(EvalError::NotEnoughOperands)
        } else if self.stack.len() > 1 {
            Err(EvalError::TooManyOperands)
        } else if let Some(res) = self.stack.pop() {
            Ok(res)
        } else {
            unreachable!()
        }
    }
}

impl TokenVisitor for EvalVisitor {
    fn visit_operation(&mut self, token: &token::Operation) {
        if self.is_error() {
            return;
        }

        match token {
            token::Operation::ADD => {
                self.apply_stack("+".to_string(), |a, b| Ok(a + b));
            }
            token::Operation::SUB => {
                self.apply_stack("-".to_string(), |a, b| Ok(a - b));
            }
            token::Operation::DIV => {
                self.apply_stack("/".to_string(), |a, b| {
                    if b == 0 {
                        Err(EvalError::DivByZero)
                    } else {
                        Ok(a / b)
                    }
                });
            }
            token::Operation::MUL => {
                self.apply_stack("*".to_string(), |a, b| Ok(a * b));
            }
        }
	debug!("Operation stack: {:?}", self.stack);
    }

    fn visit_brace(&mut self, _token: &token::Brace) {
        if self.is_error() {
            return;
        }

        self.set_error(EvalError::NonRPNExpression);
    }

    fn visit_number(&mut self, token: &token::NumberToken) {
        if self.is_error() {
            return;
        }

        self.stack.push(token.value);
	debug!("Number stack: {:?}", self.stack);
    }
}

pub fn eval(tokens: &Vec<Box<dyn Token>>) -> Result<i64, EvalError> {
    let mut visitor = EvalVisitor::new();

    for token in tokens.iter() {
        token.accept(&mut visitor);
    }

    visitor.get_result()
}
