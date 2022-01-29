mod parslib;
mod parser;
mod driver;

fn main() {
    // let args: Vec<String> = std::env::args().collect();
    // let filename = &args[1];
    // parser::parse(&std::fs::read_to_string(filename).expect("Cannot open file"));
    let res = parser::parse_stream("<stdin>", &mut std::io::stdin().lock());
}
