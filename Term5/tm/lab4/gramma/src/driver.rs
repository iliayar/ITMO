
pub mod lexer {
    #[derive(Debug)]
    pub struct Token {
	pub regex: String,
	pub expr: String,
    }

    impl Token {
	pub fn new(regex: String, expr: String) -> Self { Self { regex, expr } }
    }

    #[derive(Debug)]
    pub struct Lex {
	pub tokens: Vec<Token>,
	pub end: String,
    }

    pub struct LexBuilder {
	tokens: Vec<Token>,
	end: Option<String>,
    }

    impl LexBuilder {
	pub fn new() -> LexBuilder {
	    LexBuilder {
		tokens: Vec::new(),
		end: None,
	    }
	}

	pub fn add_token(&mut self, t: Token) -> &mut LexBuilder {
	    self.tokens.push(t);
	    return self;
	}

	pub fn end(&mut self, s: String) -> &mut LexBuilder {
	    self.end = Some(s);
	    return self;
	}

	pub fn build(self) -> Lex {
	    Lex {
		tokens: self.tokens,
		end: self.end.unwrap(),
	    }
	}
    }
}

pub mod gramma {
    use std::{collections::{HashMap, HashSet}, panic};

    #[derive(Clone,Hash,PartialEq,Eq,Debug)]
    pub struct NonTerminal {
	pub ident: String,
    }

    impl NonTerminal {
	pub fn new(ident: String) -> Self { Self { ident } }
    }

    #[derive(Clone,Hash,PartialEq,Eq,Debug)]
    pub struct Terminal {
	pub ident: String,
    }

    impl Terminal {
	pub fn new(ident: String) -> Self { Self { ident } }
    }

    #[derive(Clone,Hash,PartialEq,Eq,Debug)]
    pub enum RightElem {
	NonTerm(NonTerminal),
	Term(Terminal),
    }

    #[derive(Clone,Hash,PartialEq,Eq,Debug)]
    pub struct Rule {
	pub nonterm: NonTerminal,
	pub right: Vec<RightElem>,
    }

    impl Rule {
	pub fn new(nonterm: NonTerminal, right: Vec<RightElem>) -> Self { Self { nonterm, right } }
    }

    #[derive(Clone, Copy, Debug)]
    pub enum Assoc {
	Left,
	Right
    }

    #[derive(Debug)]
    pub struct Gramma {
	pub nonterms: HashSet<NonTerminal>,
	pub terms: HashSet<Terminal>,
	pub rules: Vec<Rule>,
	pub start: NonTerminal,
	pub end: Terminal,
	pub resolvs: Vec<(Terminal, Assoc, usize)>,
	pub term_type: HashMap<Terminal, String>,
	pub nonterm_type: HashMap<NonTerminal, String>,
	pub nonterm_eval: HashMap<Rule, String>,
	pub header: String,
	pub return_type: String,
	pub init_code: String,
	pub fin_code: String,
    }


    #[derive(Debug)]
    pub struct GrammaBuilder {
	pub nonterms: HashSet<NonTerminal>,
	pub terms: HashSet<Terminal>,
	pub rules: Vec<Rule>,
	pub start: Option<NonTerminal>,
	pub end: Option<Terminal>,
	pub resolvs: Vec<(Terminal, Assoc, usize)>,
	pub term_type: HashMap<Terminal, String>,
	pub nonterm_type: HashMap<NonTerminal, String>,
	pub nonterm_eval: HashMap<Rule, String>,
	pub header: Option<String>,
	pub return_type: Option<String>,
	pub init_code: Option<String>,
	pub fin_code: Option<String>,
	pub cur_prior: usize,
    }

    impl GrammaBuilder {

	pub fn new() -> GrammaBuilder {
	    GrammaBuilder {
		nonterms: HashSet::new(),
		terms: HashSet::new(),
		rules: Vec::new(),
		start: None,
		end: None,
		resolvs: Vec::new(),
		term_type: HashMap::new(),
		nonterm_type: HashMap::new(),
		nonterm_eval: HashMap::new(),
		header: None,
		return_type: None,
		init_code: None,
		fin_code: None,
		cur_prior: 0
	    }
	}

	pub fn nonterm(&mut self, nt: String) -> &mut Self {
	    self.nonterms.insert(NonTerminal::new(nt));
	    return self;
	}

	pub fn term(&mut self, t: String) -> &mut Self {
	    self.terms.insert(Terminal::new(t));
	    return self;
	}

	pub fn rule(&mut self, nonterm: String, right: Vec<String>) -> &mut Self {
	    let rule = self.make_rule(nonterm.clone(), right);
	    self.nonterm(nonterm);
	    self.rules.push(rule);
	    return self;
	}

	fn make_rule(&self, nonterm: String, right: Vec<String>) -> Rule {
	    let mut nright = Vec::new();
	    for r in right.into_iter() {
		if self.terms.contains(&Terminal::new(r.clone())) {
		   nright.push(RightElem::Term(Terminal::new(r)));
		} else {
		   nright.push(RightElem::NonTerm(NonTerminal::new(r)));
		}
	    }
	    return Rule::new(NonTerminal::new(nonterm), nright);
	}

	pub fn start(&mut self, nt: String) -> &mut Self {
	    if self.start.is_none() {
		self.start = Some(NonTerminal::new(nt));
	    }
	    return self;
	}

	pub fn end(&mut self, t: String) -> &mut Self {
	    if self.end.is_none() {
		self.end = Some(Terminal::new(t));
	    }
	    return self;
	}

	pub fn resolv_r(&mut self, t: String, prior: usize) -> &mut Self {
	    return self.resolv(t, Assoc::Right, prior);
	}

	pub fn resolv_l(&mut self, t: String, prior: usize) -> &mut Self {
	    return self.resolv(t, Assoc::Left, prior);
	}

	fn resolv(&mut self, t: String, assoc: Assoc, prior: usize) -> &mut Self {
	    self.resolvs.push((Terminal::new(t), assoc, prior));
	    return self;
	}

	pub fn term_type(&mut self, t: String, typ: String) -> &mut Self {
	    self.term_type.insert(Terminal::new(t), typ);
	    return self;
	}

	pub fn nonterm_type(&mut self, nt: String, typ: String) -> &mut Self {
	    self.nonterm_type.insert(NonTerminal::new(nt), typ);
	    return self;
	}

	pub fn nonterm_eval(&mut self, rule: Rule, typ: String) -> &mut Self {
	    self.nonterm_eval.insert(rule, typ);
	    return self;
	}

	pub fn header(&mut self, s: String) -> &mut Self {
	    if self.header.is_none() {
		self.header = Some(s);
	    }
	    return self;
	}

	pub fn return_type(&mut self, s: String) -> &mut Self {
	    if self.return_type.is_none() {
		self.return_type = Some(s);
	    }
	    return self;
	}

	pub fn init_code(&mut self, s: String) -> &mut Self {
	    if self.init_code.is_none() {
		self.init_code = Some(s);
	    }
	    return self;
	}

	pub fn fin_code(&mut self, s: String) -> &mut Self {
	    if self.fin_code.is_none() {
		self.fin_code = Some(s);
	    }
	    return self;
	}

	pub fn add_rule_with_eval(&mut self, nt: String, rights: Vec<(Vec<String>, Option<String>)>) -> &mut Self {
	    self.start(nt.clone());
	    for (right, eval) in rights.into_iter() {
		let rule = self.make_rule(nt.clone(), right);
		if let Some(eval) = eval {
		    self.nonterm_eval(rule.clone(), eval);
		}
		self.rules.push(rule);
	    }
	    self.nonterm(nt.clone());
	    return self;
	}

	pub fn add_prop(&mut self, prop: String, args: Vec<String>) -> &mut Self {
	    println!("Prop {:?}, Args: {:?}", prop, args);
	    match prop.as_ref() {
		"%token" => {
		    match args.len() {
			0 => panic!("Not enough arguments for %token"),
			1 => {
			    self.term(args[0].clone());
			},
			2 => {
			    if args[1] == "0" {
				self.term(args[0].clone());
				self.end(args[1].clone());
			    } else {
				self.term(args[1].clone());
				self.term_type(args[1].clone(), args[0].clone());
			    }
			},
			_ => panic!("Too many arguments for %token")
		    }
		},
		"%left" => {
		    for a in args {
			self.resolv_l(a, self.cur_prior);
		    }
		    self.cur_prior += 1;
		},
		"%right" => {
		    for a in args {
			self.resolv_r(a, self.cur_prior);
		    }
		    self.cur_prior += 1;
		},
		"%type" => {
		    match args.len() {
			0 => panic!("Not enough arguments for %type"),
			1 => panic!("Not enough arguments for %type"),
			2 => {
			    self.nonterm_type(args[1].clone(), args[0].clone());
			},
			_ => panic!("Too many arguments for %type")
		    }
		},
		"%returns" => {
		    self.return_type(args[0].clone());
		},
		_ => panic!("Unknown property {}", prop)
	    }
	    return self;
	}

	pub fn build(self) -> Gramma {
	    Gramma {
		nonterms: self.nonterms,
		terms: self.terms,
		rules: self.rules,
		start: self.start.expect("Provide at least one rule"),
		end: self.end.expect("Provide end token"),
		resolvs: self.resolvs,
		term_type: self.term_type,
		nonterm_type: self.nonterm_type,
		nonterm_eval: self.nonterm_eval,
		header: self.header.unwrap_or("".to_string()),
		return_type: self.return_type.expect("Provide return type"),
		init_code: self.init_code.unwrap_or("".to_string()),
		fin_code: self.fin_code.unwrap_or("".to_string()),
	    }
	}
    }
}
