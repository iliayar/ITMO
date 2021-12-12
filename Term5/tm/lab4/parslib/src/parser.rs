
pub struct Parser {}


impl Parser {
    pub fn new() -> Parser {
	Parser {}
    }

    pub fn parse<Token, Res, Tokens: AsRef<[Token]>>(&self, _tokens: Tokens) -> Res {
	todo!()
    }
}
