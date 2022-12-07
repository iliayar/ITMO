use crate::token;
use crate::TokenVisitor;

pub struct PrintVisitor<'a> {
    writer: &'a mut dyn std::io::Write,
}

impl<'a> PrintVisitor<'a> {
    pub fn new(writer: &'a mut dyn std::io::Write) -> Self {
        PrintVisitor { writer }
    }

    fn write<S: AsRef<str>>(&mut self, s: S) {
        write!(self.writer, "{}", s.as_ref()).ok();
    }
}

impl<'a> TokenVisitor for PrintVisitor<'a> {
    fn visit_operation(&mut self, token: &token::Operation) {
        self.write(match token {
            ADD => " + ",
            SUB => " - ",
            DIV => " / ",
            MUL => " * ",
        });
    }

    fn visit_brace(&mut self, token: &token::Brace) {
        self.write(match token {
            LEFT => "(",
            RIGHT => ")",
        });
    }

    fn visit_number(&mut self, token: &token::NumberToken) {
        self.write(format!("{}", token.value))
    }
}
