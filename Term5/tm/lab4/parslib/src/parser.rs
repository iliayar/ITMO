use std::fmt::Debug;
use termion::*;

pub trait TokenStream<T> {
    fn lookahead(&self) -> &T;
    fn pop(&mut self) -> T;
    fn init(&mut self);
}

pub trait TokenStreamDebug<T> {
    fn print(&self);
}

impl<T: Debug> TokenStreamDebug<T> for Vec<T> {
    fn print(&self) {
	for t in self.iter().rev() {
	    print!(" {}{:?}{}", color::Fg(color::Red), t, style::Reset);
	}
    }
}

impl<T> TokenStream<T> for Vec<T> {
    fn lookahead(&self) -> &T {
        self.last().expect("Token stack is empty")
    }

    fn pop(&mut self) -> T {
	self.pop().expect("Token stack is empty")
    }

    fn init(&mut self) {
	self.reverse();
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
    goto: Box<dyn Fn(usize, &NT) -> Option<usize>>,
}

impl<T, NT, TS: TokenStream<T>> Parser<T, NT, TS> {
    pub fn new<F>(token_stack: TS, goto: F) -> Parser<T, NT, TS>
	where F: Fn(usize, &NT) -> Option<usize> + 'static
    {
	let mut token_stack = token_stack;
	token_stack.init();
	Parser {
	    stack: vec![StackElement::State(0)],
	    token_stack,
	    goto: Box::new(goto),
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

    pub fn accepted(&self) -> bool {
	self.stack.is_empty()
    }

    pub fn state(&self) -> usize {
	if let StackElement::State(state) = self.stack.last()
	    .expect("Cannot get state of empty stack") {
		return *state;
	    }
	panic!("Top of the stack is not state. Invariant broken");
    }

    pub fn lookahead(&self) -> &T {
	self.token_stack.lookahead()
    }

    pub fn shift(&mut self, state: usize) {
	self.stack.push(StackElement::Token(self.token_stack.pop()));
	self.push_state(state);
    }

    pub fn reduce<RF>(&mut self, len: usize, fun: RF)
    where RF: FnOnce(Vec<StackElement<T, NT>>) -> NT
    {
	let mut res = Vec::new();
	for _ in 0..len {
	    self.pop_state();
	    res.push(self.stack.pop().expect("Lack off elements to reduce"));
	}
	let state = self.pop_state();
	let nt = fun(res);
	let nstate = (self.goto)(state, &nt);

	if let Some(nstate) = nstate {
	    self.push_state(state);
	    self.stack.push(StackElement::NonTerminal(nt));
	    self.push_state(nstate);
	}
    }
}


pub fn print_parser_state<T, NT, TS>(parser: &Parser<T, NT, TS>)
    where TS: TokenStream<T> + TokenStreamDebug<T>, T: Debug, NT: Debug
{
    for e in parser.stack.iter() {
	print_stack_element(e);
	print!(" ");
    }

    print!("|");

    parser.token_stack.print();

    println!("");
}

fn print_stack_element<T: Debug, NT: Debug>(e: &StackElement<T, NT>) {
    match e {
	StackElement::State(state) => {
	    print!("{}{}{}", color::Fg(color::Blue), state, style::Reset);
	},
	StackElement::NonTerminal(nt) => {
	    print!("{}{:?}{}", color::Fg(color::Green), nt, style::Reset);
	},
	StackElement::Token(t) => {
	    print!("{}{:?}{}", color::Fg(color::Red), t, style::Reset);
	},
    }
}
