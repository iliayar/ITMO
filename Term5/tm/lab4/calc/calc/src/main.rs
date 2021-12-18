mod parslib;
mod parser;

fn main() {
    let res = parser::parse("
1 + 2 - 3 - 4 * 5 / ( 1 + 2 * 3 )
");
    println!("{}", res);
}
