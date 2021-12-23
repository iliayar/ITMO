mod parslib;
mod parser;

fn main() {
//     let res = parser::parse("<string>", "
// 1 + 2 - 3 - 4 * 5 / ( 1 + 2 * 3 )
// ");

    parser::parse_stream("<stdin>", &mut std::io::stdin().lock());
    // println!("{}", res);
}
