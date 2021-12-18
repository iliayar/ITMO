mod lexer;
mod gramma;
mod driver;

fn main() {
    let gramma = gramma::parse(r#"

%option "asdads"
%option "123" "567"
%header %{
   println!("XUY");
%}

%%


asd : aboba abiba
    | xuy
    | this is code %{ return XUY; %}
    ;

%%

"#);

    println!("{:?}", gramma);
}
