use crate::token;
use crate::Token;
use crate::TokenVisitor;

#[derive(Debug)]
pub enum Assoc {
    Left,
    Right,
}

#[derive(Debug)]
pub enum Matched {
    OpenBrace,
    CloseBrace,
    Operator { prior: usize, assoc: Assoc },
    None,
}

struct MatchVisitor {
    matched: Matched,
}

impl MatchVisitor {
    pub fn new() -> Self {
        Self {
            matched: Matched::None,
        }
    }
}

impl TokenVisitor for MatchVisitor {
    fn visit_operation(&mut self, token: &token::Operation) {
        self.matched = match token {
            token::Operation::ADD => Matched::Operator {
                prior: 1,
                assoc: Assoc::Left,
            },
            token::Operation::SUB => Matched::Operator {
                prior: 1,
                assoc: Assoc::Left,
            },
            token::Operation::DIV => Matched::Operator {
                prior: 0,
                assoc: Assoc::Left,
            },
            token::Operation::MUL => Matched::Operator {
                prior: 0,
                assoc: Assoc::Left,
            },
        };
    }

    fn visit_brace(&mut self, token: &token::Brace) {
        self.matched = match token {
            token::Brace::LEFT => Matched::OpenBrace,
            token::Brace::RIGHT => Matched::CloseBrace,
        };
    }

    fn visit_number(&mut self, _token: &token::NumberToken) {}
}

pub fn match_token(token: &dyn Token) -> Matched {
    let mut visitor = MatchVisitor::new();
    token.accept(&mut visitor);
    visitor.matched
}
