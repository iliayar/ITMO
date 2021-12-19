use std::fs;

pub fn put_parslib(path: &str) {
    fs::create_dir(format!("{}/src/parslib", path)).ok();

    fs::write(format!("{}/src/parslib/mod.rs", path), r#"
#![allow(dead_code)]
pub mod parser;
pub mod lexer;


mod util;
pub use util::*;
"#).ok();
    fs::write(format!("{}/src/parslib/lexer.rs", path), r#"

use std::{io::BufRead, collections::VecDeque};

use fancy_regex::Regex;

pub struct Token<T> {
    pub token: T,
    pub pos: (usize, usize),
}

impl<T> Token<T> {
    pub fn new(token: T, pos: (usize, usize)) -> Self { Self { token, pos } }
}

pub struct Lexer<T>
{
    lexems: Vec<Lexem<T>>,
    end: T,
}

#[derive(Debug)]
pub enum LexerError
{
    InvalidToken(usize),
}

pub struct StreamLexer<'a, R: BufRead, T, FE: Fn(LexerError, String) -> ()> {
    source: &'a mut R,
    lexems: Vec<Lexem<T>>,
    end: Option<T>,
    pub buf: VecDeque<Token<T>>,
    pos: usize,
    onerror: FE,
    pub all_input: Option<String>,
}

impl<'a, R: BufRead, T, FE: Fn(LexerError, String) -> ()> StreamLexer<'a, R, T, FE> {

    pub fn fill(&mut self) {
	if self.buf.len() > 0 || self.end.is_none() {
	    return;
	}

	let mut input = String::new();
	let res =  self.source.read_line(&mut input);

	if let Ok(n) = res {
	    if n == 0 {
		self.buf.push_back(Token::new(self.end.take().unwrap(), (self.pos, self.pos)));
		return;
	    }
	} else if let Err(e) = res {
	    panic!("Failed to read input: {}", e);
	}

	self.all_input.as_mut().unwrap().push_str(&input);

	let mut input: &str = input.as_ref();

	'input_read: while input.len() > 0 {
	    for lexem in self.lexems.iter() {
		if let Some((ninput, token)) = lexem.mtch(input) {
		    let pos_delta = input.len() - ninput.len();
		    assert!(pos_delta > 0, "Empty match");
		    input = ninput;
		    if let Some(token) = token {
			self.buf.push_back(Token::new(token, (self.pos, self.pos + pos_delta)));
		    }
		    self.pos += pos_delta;
		    continue 'input_read;
		}
	    }
	    (self.onerror)(LexerError::InvalidToken(self.pos + 1), self.all_input.take().unwrap());
	}
    }
}

impl<T> Lexer<T>
{
    pub fn new(end: T) -> Lexer<T> {
	Lexer {
	    lexems: Vec::<Lexem<T>>::new(),
	    end,
	}
    }

    pub fn add<S: AsRef<str>, Fun: Fn(String) -> Option<T> + 'static>(&mut self, regex: S, token: Fun) {
	if let Ok(regex) = Regex::new(regex.as_ref()) {
	    self.lexems.push(Lexem::new(regex, token));
	} else {
	    panic!("Invalid regex: {}\nRegex are checked at generation step. This is mostly programmer's fault", regex.as_ref());
	}
    }

    pub fn lex_stream<'a, R: BufRead, FE: Fn(LexerError, String) -> ()>(self, source: &'a mut R, onerror: FE) -> StreamLexer<'a, R, T, FE> {
	StreamLexer {
	    source,
	    lexems: self.lexems,
	    end: Some(self.end),
	    buf: VecDeque::new(),
	    pos: 0,
	    onerror,
	    all_input: Some(String::new()),
	}
    }

    pub fn lex<S: AsRef<str>>(self, sinput: S) -> Result<(Vec<Token<T>>, S), LexerError> {
	let mut input: &str = sinput.as_ref();
	let mut res: Vec<Token<T>> = Vec::new();
	let mut pos: usize = 0;

	'input_read: while input.len() > 0 {
	    for lexem in self.lexems.iter() {
		if let Some((ninput, token)) = lexem.mtch(input) {
		    let pos_delta = input.len() - ninput.len();
		    assert!(pos_delta > 0, "Empty match");
		    input = ninput;
		    if let Some(token) = token {
			res.push(Token::new(token, (pos, pos + pos_delta)));
		    }
		    pos += pos_delta;
		    continue 'input_read;
		}
	    }
	    return Err(LexerError::InvalidToken(pos + 1));
	}

	res.push(Token::new(self.end, (pos, pos)));
	return Ok((res, sinput));
    }
}

pub struct Lexem<T> {
    regex: Regex,
    token: Box<dyn Fn(String) -> Option<T>>,
}

impl<T> Lexem<T> {
    pub fn new<Fun: Fn(String) -> Option<T> + 'static>(regex: Regex, token: Fun) -> Lexem<T> {
	Lexem {
	    regex,
	    token: Box::new(token),
	}
    }

    pub fn mtch<'a>(&self, input: &'a str) -> Option<(&'a str, Option<T>)> {
	if let Ok(Some(mtch)) = self.regex.find(input) {
	    if mtch.start() == 0 {
		Some((
		    &input[mtch.end()..],
		    (self.token)(mtch.as_str().to_string()),
		))
	    } else {
		None
	    }
	} else {
	    None
	}
    }
}
"#).ok();

    fs::write(format!("{}/src/parslib/parser.rs", path), r#"

use std::{fmt::Debug, io::BufRead};
use termion::*;

use super::{lexer::{self, StreamLexer, LexerError}, prety_print_error_range};

pub trait TokenStream<T> {
    fn lookahead(&mut self) -> &T;
    fn pop(&mut self) -> T;
    fn init(&mut self);
    fn error_top(&mut self, filename: &str, msg: &str);
}

pub trait TokenStreamDebug<T> {
    fn print(&self);
}

impl<T: Debug> TokenStreamDebug<T> for Vec<lexer::Token<T>> {
    fn print(&self) {
	for t in self.iter().rev() {
	    print!(" {}{:?}{}", color::Fg(color::Red), t.token, style::Reset);
	}
    }
}

impl<T, S: AsRef<str>> TokenStream<T> for (Vec<lexer::Token<T>>, S) {
    fn lookahead(&mut self) -> &T {
        &self.0.last().expect("Token stack is empty").token
    }

    fn pop(&mut self) -> T {
	self.0.pop().expect("Token stack is empty").token
    }

    fn init(&mut self) {
	self.0.reverse();
    }

    fn error_top(&mut self, filename: &str, msg: &str) {
	if let Some(token) = self.0.last() {
	    prety_print_error_range(filename, self.1.as_ref(), token.pos.0, Some(token.pos.1), msg)
	} else {
	    panic!("Stack is empty. Cannot report location")
	}
    }
}

impl<'a, R: BufRead, T, FE: Fn(LexerError, String) -> ()> TokenStream<T> for StreamLexer<'a, R, T, FE> {
    fn lookahead(&mut self) -> &T {
        self.fill();
	return &self.buf.front().expect("Token stack is empty").token;
    }

    fn pop(&mut self) -> T {
        self.fill();
	return self.buf.pop_front().expect("Token stack is empty").token;
    }

    fn init(&mut self) {
        self.fill();
    }

    fn error_top(&mut self, filename: &str, msg: &str) {
	if let Some(token) = self.buf.front() {
	    prety_print_error_range(filename, self.all_input.as_ref().unwrap(), token.pos.0, Some(token.pos.1), msg)
	} else {
	    panic!("Stack is empty. Cannot report location")
	}
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

    pub fn panic_location(&mut self, filename: &str, msg: &str) {
	self.token_stack.error_top(filename, msg);
	panic!("{}", msg);
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

    pub fn lookahead(&mut self) -> &T {
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
"#).ok();
    fs::write(format!("{}/src/parslib/util.rs", path), r#"
use super::lexer::LexerError;
use termion::*;

const NEAR_LINES: usize = 1;

pub fn get_near_lines(input: &str, pos: usize) -> (usize, Vec<&str>, usize, usize) {
    let lines: Vec<&str> = input.lines().collect();
    let mut i = 0usize;
    let mut linen = 0usize;
    for (line, n) in lines.iter().zip(0..) {
	if i + line.len() + 1 >= pos {
	    linen = n;
	    break;
	} else {
	    i += line.len() + 1;
	}
    }
    let pos_in_line = pos - i;

    let begin = linen - NEAR_LINES.min(linen);
    let end = (linen + NEAR_LINES + 1).min(lines.len());
    return (
	begin,
	lines[begin..end].to_vec(),
	linen - begin,
	pos_in_line,
    );
}


pub fn prety_print_error_range(filename: &str, input: &str, begin: usize, end: Option<usize>, msg: &str) {
    let repeat_str = |c: char, n: usize| std::iter::repeat(c).take(n).collect::<String>();

    let (begin_line, lines, linen, linepos) = get_near_lines(input, begin);
    let mut max_num_len = format!("{}", begin_line + lines.len() + 1).len();
    if let Some(end) = end {
	let (begin_line, lines, _, _) = get_near_lines(input, end);
	max_num_len = format!("{}", begin_line + lines.len() + 1).len();
    }
    let prefix_str = |s: &str| format!("{}{}{:>w$} | {}", style::Bold, color::Fg(color::LightBlue), s, style::Reset, w = max_num_len);
    let prefix = |n: usize, begin: usize| prefix_str(&format!("{}", begin + n + 1));
    let underline_line = |i, lines: &[&str], begin_line: usize, begin: usize, end: usize, msg: &str| {
	eprintln!("{}{}", prefix(i, begin_line), lines[i]);
	eprintln!("{}{}{}{}{} {}{}",
		  prefix_str(""), color::Fg(color::Red), style::Bold,
		  repeat_str(' ', begin - 1),
		  repeat_str('^', end + 1 - begin),
		  msg, style::Reset);
    };

    let mut i = 0usize;
    eprintln!("{}{}{} -->{} {}:{}:{}",
	      repeat_str(' ', max_num_len - 1), color::Fg(color::LightBlue), style::Bold,
	      style::Reset, filename, begin_line + linen + 1, linepos
    );
    while i < linen && i < lines.len() {
	eprintln!("{}{}", prefix(i, begin_line), lines[i]);
	i += 1;
    }
    if let Some(end) = end {
	let mut cur_linepos = linepos;
	let (end_begin_line, end_lines, end_linen, end_linepos) = get_near_lines(input, end);
	while i < lines.len() && i + begin_line < end_begin_line {
	    underline_line(i, &lines, begin_line, cur_linepos, lines[i].len(), "");
	    i += 1;
	    cur_linepos = 1;
	}
	if i + begin_line < end_begin_line {
	    eprintln!("{}{}{} ...{}",
		      repeat_str(' ', max_num_len - 1), color::Fg(color::LightBlue), style::Bold,
		      style::Reset);
	}
	i = (begin_line + i).max(end_begin_line) - end_begin_line;
	while i < end_linen && i < end_lines.len() {
	    underline_line(i, &end_lines, end_begin_line, cur_linepos, end_lines[i].len(), "");
	    i += 1;
	    cur_linepos = 1;
	}
	underline_line(i, &end_lines, end_begin_line, cur_linepos, end_linepos, msg);
	i += 1;
	while i < end_lines.len() {
	    eprintln!("{}{}", prefix(i, end_begin_line), end_lines[i]);
	    i += 1;
	}
    } else {
	underline_line(i, &lines, begin_line, linepos, linepos, msg);
	i += 1;
	while i < lines.len() {
	    eprintln!("{}{}", prefix(i, begin_line), lines[i]);
	    i += 1;
	}
    }
}

pub fn prety_print_error_at(filename: &str, input: &str, pos: usize, msg: &str) {
    prety_print_error_range(filename, input, pos, None, msg);
}

pub fn prety_print_err_line(msg: &str) {
    eprintln!("{}{}error{}{}: {}{}", style::Bold, color::Fg(color::Red), style::Reset, style::Bold, msg, style::Reset);
}

pub fn prety_print_lex_error(filename: &str, input: &str, err: LexerError) {
    match err {
	LexerError::InvalidToken(pos) => prety_print_invalid_token(filename, input, pos),
    };
}

pub fn prety_print_invalid_token(filename: &str, input: &str, pos: usize) {
    prety_print_err_line("Invalid token met. Could not match any regex");
    prety_print_error_at(filename, input, pos, "could not match token");
}
"#).ok();
}
