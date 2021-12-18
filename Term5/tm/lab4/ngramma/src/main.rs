mod lexer;
mod gramma;
mod driver;

fn main() {
    let gramma = gramma::parse(r#"

%{
   println!("XUY");
%}

%token END "0"

%returns "()"

%%


asd : aboba abiba
    | xuy
    | this is code %{ return XUY; %}
    ;

%%

"#);

    println!("{:?}", gramma);
}
