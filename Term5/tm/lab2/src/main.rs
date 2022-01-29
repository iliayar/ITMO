mod tokenizer;
mod parser;
mod drawer;

use parser::*;
use drawer::*;
use std::io::{BufReader, stdin};

fn main() {
    let mut parser = Parser::new();
    // let res = parser.parse_str("void f(int *a, float ** b, double c);".to_owned());
    let res = parser.parse(Box::new(BufReader::new(stdin())));
    draw_tree(&res, "graphs/gen.dot");
}
