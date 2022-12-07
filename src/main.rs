
mod lib;
pub use lib::*;

fn prnt(tkn: &dyn token::Token) {
    let mut stdout = std::io::stdout().lock();
    let mut visitor = PrintVisitor::new(&mut stdout);

    tkn.accept(&mut visitor);
}

fn main() {
    let add = token::Operation::ADD;
    prnt(&add);
}
