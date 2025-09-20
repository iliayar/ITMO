use crate::token;
use crate::Token;
use crate::TokenVisitor;

use log::*;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum PrintError {
    #[error("Write IO error: {0}")]
    IOError(#[from] std::io::Error),
}

struct PrintVisitor<'a> {
    writer: &'a mut dyn std::io::Write,
    err: Option<PrintError>,
}

impl<'a> PrintVisitor<'a> {
    pub fn new(writer: &'a mut dyn std::io::Write) -> Self {
        PrintVisitor { writer, err: None }
    }

    fn write<S: AsRef<str>>(&mut self, s: S) {
        if let Err(err) = write!(self.writer, "{}", s.as_ref()) {
            self.err = Some(err.into());
        }
    }
}

impl<'a> TokenVisitor for PrintVisitor<'a> {
    fn visit_operation(&mut self, token: &token::Operation) {
        self.write(match token {
            token::Operation::ADD => "+",
            token::Operation::SUB => "-",
            token::Operation::DIV => "/",
            token::Operation::MUL => "*",
        });
    }

    fn visit_brace(&mut self, token: &token::Brace) {
        self.write(match token {
            token::Brace::LEFT => "(",
            token::Brace::RIGHT => ")",
        });
    }

    fn visit_number(&mut self, token: &token::NumberToken) {
        self.write(format!("{}", token.value))
    }
}

pub fn print_token<'a>(
    token: &dyn Token,
    writer: &'a mut dyn std::io::Write,
) -> Result<(), PrintError> {
    let mut visitor = PrintVisitor::new(writer);
    token.accept(&mut visitor);

    if let Some(err) = visitor.err {
        Err(err)
    } else {
        Ok(())
    }
}
