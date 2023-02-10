use crate::token;
use crate::Token;
use crate::TokenVisitor;

#[derive(Debug)]
pub enum Assoc {
    Left,
    Right,
}

#[derive(Debug)]
pub enum TokenType {
    OpenBrace,
    CloseBrace,
    Operator { prior: usize, assoc: Assoc },
    None,
}

struct TokenTypeVisitor {
    matched: TokenType,
}

impl TokenTypeVisitor {
    pub fn new() -> Self {
        Self {
            matched: TokenType::None,
        }
    }
}

impl TokenVisitor for TokenTypeVisitor {
    fn visit_operation(&mut self, token: &token::Operation) {
        self.matched = match token {
            token::Operation::ADD => TokenType::Operator {
                prior: 1,
                assoc: Assoc::Left,
            },
            token::Operation::SUB => TokenType::Operator {
                prior: 1,
                assoc: Assoc::Left,
            },
            token::Operation::DIV => TokenType::Operator {
                prior: 0,
                assoc: Assoc::Left,
            },
            token::Operation::MUL => TokenType::Operator {
                prior: 0,
                assoc: Assoc::Left,
            },
        };
    }

    fn visit_brace(&mut self, token: &token::Brace) {
        self.matched = match token {
            token::Brace::LEFT => TokenType::OpenBrace,
            token::Brace::RIGHT => TokenType::CloseBrace,
        };
    }

    fn visit_number(&mut self, _token: &token::NumberToken) {}
}

pub fn token_type(token: &dyn Token) -> TokenType {
    let mut visitor = TokenTypeVisitor::new();
    token.accept(&mut visitor);
    visitor.matched
}
