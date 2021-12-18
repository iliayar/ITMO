mod parslib;
mod parser;

#[derive(Debug,PartialEq,Clone)]
pub enum Token {
    IDENTIFIER(String),
    LPAREN,
    RPAREN,
    COMMA,
    ASTERISK,
    SEMICOLON,
    END,
}

#[derive(Debug,PartialEq,Clone)]
pub enum NodeValue {
    NonTerminal(String),
    Terminal(Token),
}

#[derive(Debug,PartialEq,Clone)]
pub struct Tree {
    pub value: NodeValue,
    pub childs: Vec<Tree>,
}

impl Tree {
    fn new(value: NodeValue, childs: Vec<Tree>) -> Tree {
	Tree { value, childs }
    }
    fn node(value: NodeValue) -> Tree {
	Tree::new(value, vec![])
    }
}


fn main() {
    let res = parser::parse("void f (int *a, float ** b, double c);");

    println!("{:?}", res);
}
