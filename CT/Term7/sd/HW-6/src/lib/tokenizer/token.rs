use crate::TokenVisitor;

use log::*;

pub trait Token {
    fn accept(&self, visitor: &mut dyn TokenVisitor);
}

#[derive(Debug, Clone, Copy)]
pub enum Brace {
    LEFT,
    RIGHT,
}

#[derive(Debug, Clone, Copy)]
pub enum Operation {
    ADD,
    SUB,
    DIV,
    MUL,
}

#[derive(Debug, Clone, Copy)]
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
