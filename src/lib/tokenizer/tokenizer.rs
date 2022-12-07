use thiserror::Error;

#[derive(Error, Debug)]
pub enum TokenizerError {
}

type Source<'a> = std::str::Chars<'a>;

trait State {
    fn handle(self: Box<Self>) -> Box<dyn State>;
}

struct Start<'a> {
    src: Source<'a>,
}
