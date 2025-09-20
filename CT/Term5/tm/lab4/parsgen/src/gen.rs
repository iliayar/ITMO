use std::collections::{HashSet, HashMap};

use gramma::{Rule, RightElem, NonTerminal, Gramma, Terminal};
use termion::*;

use crate::lalr::{StateMachine, print_state_machine};

use super::codegen::Generator;

impl Generator {

    pub fn generate_ctrl_table(&mut self) {
	self.replace_entry_rule();
	self.calc_util();
	self.calc_eps();
	self.calc_first();
	self.state_machine = Some(StateMachine::new(&self));
	if self.gramma.debug {
	    self.print_debug();
	}
    }

    fn calc_util(&mut self) {
	// Init FIRST and FOLLOW
	for t in self.gramma.nonterms.iter() {
	    self.FIRST.insert(t.clone(), HashSet::new());
	}
    }

    pub fn has_eps(&self, t: &NonTerminal) -> bool {
	return self.eps_rule.contains(&t);
    }

    fn calc_eps(&mut self) {
	loop {
	    let mut changed = false;
	    for rule in self.gramma.rules.iter() {
		let mut eps = true;
		for r in rule.right.iter() {
		    match &r {
			RightElem::Term(_) => { eps = false; },
			RightElem::NonTerm(t) => { eps = eps && self.has_eps(t); },
		    }
		}
		if eps {
		    changed = changed || self.eps_rule.insert(rule.nonterm.clone());
		}
	    }
	    if !changed {
		break;
	    }
	}
    }

    pub fn first<TS: AsRef<[RightElem]>>(&self, s: TS) -> HashSet<Terminal> {
	let mut res = HashSet::new();

	for r in s.as_ref().iter() {
	    match &r {
		&RightElem::Term(t) => {
		    res.insert(t.clone());
		    break;
		},
		&RightElem::NonTerm(nt) => {
		    if self.FIRST.get(&nt).is_none() {
			panic!("Unknown non temrinal {}", nt.ident);
		    }
		    res = res.union(&self.FIRST[nt]).cloned().collect();
		    if !self.has_eps(nt) {
			break;
		    }
		}
	    }
	}

	return res;
    }

    fn calc_first(&mut self) {
	loop {
	    let mut changed = false;
	    for rule in self.gramma.rules.iter() {
		for t in self.first(&rule.right) {
		    changed = changed || self.FIRST.get_mut(&rule.nonterm).unwrap().insert(t);
		}
	    }
	    if !changed {
		break;
	    }
	}
    }

    fn replace_entry_rule(&mut self) {
	let mut nstart = NonTerminal::new("S".to_string());
	'find_start: loop {
	    for r in self.gramma.rules.iter() {
		if r.nonterm.ident == nstart.ident {
		    nstart = NonTerminal::new(nstart.ident.to_owned() + "S");
		    continue 'find_start;
		}
	    }
	    break;
	}

	let start = &self.gramma.start;
	self.gramma.rules.push(Rule::new(nstart.clone(), vec![RightElem::NonTerm(start.clone())]));
	self.gramma.nonterms.insert(nstart.clone());
	self.gramma.start = nstart;
    }

    fn print_debug(&self) {
	println!("======================== INFO ==============================");
	print_gramma(&self.gramma);
	println!("------------------------------------------------------------");
	print_eps(&self.gramma.nonterms, &self.eps_rule);
	println!("------------------------ FIRST -----------------------------");
	print_first(&self.FIRST);
	println!("------------------------------------------------------------");
	println!("===================== STATE MACHINE ========================");
	print_state_machine(self.state_machine.as_ref().unwrap());
	println!("------------------------------------------------------------");
    }

}

fn print_first(first: &HashMap<NonTerminal, HashSet<Terminal>>) {
    for (nt, t) in first.iter() {
	print!("{}{}{}:", color::Fg(color::LightBlue), nt.ident, style::Reset);
	for t in t.iter() {
	    print!(" {}{}{}", color::Fg(color::LightGreen), t.ident, style::Reset);
	}
	println!("");
    }
}

fn print_eps(nonterms: &HashSet<NonTerminal>, eps_rules: &HashSet<NonTerminal>) {
    print!("{}EPS{}:", color::Fg(color::LightBlue), style::Reset);
    for t in nonterms.iter() {
	if eps_rules.contains(&t) {
	    print!(" {}{}{}", color::Fg(color::LightGreen), t.ident, style::Reset);
	} else {
	    print!(" {}{}{}", color::Fg(color::LightRed), t.ident, style::Reset);
	}
    }
    println!("");
}

fn print_gramma(gramma: &Gramma) {
    for rule in gramma.rules.iter() {
	print_rule(rule);
	println!("");
    }
}

pub fn print_rule(rule: &Rule) {
    print!("{}{}{} ->", color::Fg(color::LightBlue), rule.nonterm.ident, style::Reset);
    for r in rule.right.iter() {
	print_right_elem(r);
    }
    if rule.right.len() == 0 {
	print!(" ε");
    }
}

pub fn print_right_elem(r: &RightElem) {
    match &r {
	&RightElem::NonTerm(nonterm) => {
	    print!(" {}{}{}", color::Fg(color::LightGreen), nonterm.ident, style::Reset);
	},
	&RightElem::Term(term) => {
	    print!(" {}{}{}", color::Fg(color::LightRed), term.ident, style::Reset);
	},
    }
}
