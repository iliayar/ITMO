use lib::parser::*;
use lib::lexer::*;

#[derive(Debug)]
enum Test {
    A,
    B,
    C(String),
    D(String, i32),
}

pub fn parse(_inp: &dyn std::io::Read) -> Gramma {

    let mut lexems = Lexer::new();
    lexems.add(r"A", |_| Test::A);
    lexems.add(r"B", |_| Test::B);
    lexems.add(r"C", |s| Test::C(s));
    lexems.add(r"D1", |s| Test::D(s, 1));
    lexems.add(r"D2", |s| Test::D(s, 2));

    let res = lexems.lex("AD1D2BCD1");
    println!("{:?}", res);
    todo!();
}
