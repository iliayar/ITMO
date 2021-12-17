mod lexer;
mod driver;

fn main() {
    let lex = lexer::parse(r#"

%end "asdads"

%%

"\s+" { return format!("{}", 123); }

"[a-zA-Z_][a-zA-Z0-9_]+" {}

%%

"#);

    println!("{:?}", lex);
}
