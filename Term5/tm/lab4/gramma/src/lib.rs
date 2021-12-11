use lib::parser::*;
use lib::lexer::*;
use lib::*;

#[derive(Debug)]
enum Test {
    A,
    B,
    C(String),
    D(String, i32),
    WS,
}

pub struct Gramma {

}

pub fn parse(_inp: &dyn std::io::Read) -> Gramma {

    let mut lexems = Lexer::new();
    lexems.add(r"A", |_| Test::A);
    lexems.add(r"B", |_| Test::B);
    lexems.add(r"C", |s| Test::C(s));
    lexems.add(r"D1", |s| Test::D(s, 1));
    lexems.add(r"D2", |s| Test::D(s, 2));
    lexems.add(r"\s+", |_| Test::WS);

    let input = "AB






D1D2
CD3A
BC D1";
    let tokens = match lexems.lex(input) {
	Ok(res) => res,
	Err(lex_err) => {
	    prety_print_lex_error("stdin", input, lex_err);
	    panic!("Failed to lex file");
	},
    };


    let mut parser = Parser::new();

    todo!();
}
