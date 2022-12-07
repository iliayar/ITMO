use crate::TokenVisitor;

pub trait Token {
    fn accept(&self, visitor: &mut dyn TokenVisitor);
}

pub enum Brace {
    LEFT,
    RIGHT,
}

pub enum Operation {
    ADD,
    SUB,
    DIV,
    MUL,
}

pub struct NumberToken {
    pub value: i64,
}

impl Token for Brace {
    fn accept(&self, visitor: &mut dyn TokenVisitor) {
        visitor.visit_brace(self);
    }
}

impl Token for NumberToken {
    fn accept(&self, visitor: &mut dyn TokenVisitor) {
        visitor.visit_number(self);
    }
}

impl Token for Operation {
    fn accept(&self, visitor: &mut dyn TokenVisitor) {
        visitor.visit_operation(self);
    }
}
