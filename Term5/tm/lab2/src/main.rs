mod tokenizer;
mod parser;
mod drawer;

use parser::*;
use drawer::*;

fn main() {
    let mut parser = Parser::new();
    let res = parser.parse_str("void f(int *a, float ** b, double c);".to_owned());
    draw_tree(&res, "graphs/gen.dot");
}
