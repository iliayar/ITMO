
use crate::token;

pub trait TokenVisitor {
    fn visit_operation(&mut self, token: &token::Operation);
    fn visit_brace(&mut self, token: &token::Brace);
    fn visit_number(&mut self, token: &token::NumberToken);
}
