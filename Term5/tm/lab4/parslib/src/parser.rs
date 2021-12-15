
pub trait TokenStream<T> {
    fn lookahead(&self) -> &T;
    fn pop(&mut self) -> T;
}

impl<T> TokenStream<T> for Vec<T> {
    fn lookahead(&self) -> &T {
        self.last().expect("Token stack is empty")
    }

    fn pop(&mut self) -> T {
	self.pop().expect("Token stack is empty")
    }
}

pub enum StackElement<T, NT> {
    State(usize),
    Token(T),
    NonTerminal(NT),
}

pub struct Parser<T, NT, TS: TokenStream<T>> {
    stack: Vec<StackElement<T, NT>>,
    token_stack: TS,
}

impl<T, NT, TS: TokenStream<T>> Parser<T, NT, TS> {
    pub fn new(token_stack: TS) -> Parser<T, NT, TS> {
	Parser {
	    stack: vec![StackElement::State(0)],
	    token_stack
	}
    }

    fn push_state(&mut self, state: usize) {
	self.stack.push(StackElement::State(state));
    }

    fn pop_state(&mut self) -> usize {
	if let Some(StackElement::State(state)) = self.stack.pop() {
	    return state;
	};
	panic!("No state on the stack");
    }

    pub fn lookahead(&self) -> &T {
	self.token_stack.lookahead()
    }

    pub fn shift(&mut self, state: usize) {
	self.stack.push(StackElement::Token(self.token_stack.pop()));
	self.push_state(state);
    }

    pub fn reduce<F>(&mut self, len: usize, fun: F)
    where F: Fn(Vec<StackElement<T, NT>>) -> StackElement<T, NT>
    {
	let mut res = Vec::new();
	for _ in 0..len {
	    self.pop_state();
	    res.push(self.stack.pop().expect("Lack off elements to reduce"));
	}
	res.reverse();
	self.stack.push(fun(res));
	todo!("How will be better?");
    }
}
