use std::{collections::{HashSet, HashMap}, iter::FromIterator, hash::Hash, panic};

use gramma::{Rule, Terminal, NonTerminal, Gramma, RightElem, Assoc};
use termion::*;

use crate::{codegen::Generator, gen::{print_right_elem, print_rule}, utils::{perror, pwarning}};

#[derive(Clone,Debug)]
pub enum Action {
    Shift(usize),
    Reduce(Rule),
}

impl Action {
    pub fn check_conflic(&self, other: &Action) -> Result<(), String> {
	match &self {
	    &Action::Shift(id) => {
		match &other {
		    &Action::Shift(oid) => {
			if id != oid {
			    Err("shift-shift confict".to_string())
			} else {
			    Ok(())
			}
		    },
		    &Action::Reduce(_) => {
			Err("shift-reduce coflict".to_string())
		    }
		}
	    },
	    &Action::Reduce(rule) => {
		match &other {
		    &Action::Shift(_) => {
			Err("shift-reduce coflict".to_string())
		    },
		    &Action::Reduce(orule) => {
			if rule != orule {
			    Err("reduce-reduce confict".to_string())
			} else {
			    Ok(())
			}
		    }
		}
	    }
	}
    }
}

#[derive(Clone,Debug)]
pub struct Item {
    pub rule: Rule,
    pub dot: usize,
    pub la: HashSet<Terminal>,
}

impl PartialEq for Item {
    fn eq(&self, other: &Self) -> bool {
        self.rule == other.rule && self.dot == other.dot
    }
}
impl Eq for Item { }

impl Hash for Item {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.rule.hash(state);
        self.dot.hash(state);
    }
}

impl Item {
    pub fn new(rule: Rule, dot: usize, la: HashSet<Terminal>) -> Self { Self { rule, dot, la } }

    fn get_la(&self, gen: &Generator) -> HashSet<Terminal> {
	let right = if self.dot + 1 >= self.rule.right.len() {
	    &self.rule.right[..0] // It's likely empty
	} else {
	    &self.rule.right[self.dot+1..]
	};
	let mut vec = right.to_vec();
	let mut res = HashSet::new();

	for t in self.la.iter() {
	    vec.push(RightElem::Term(t.clone()));
	    res = res.union(&gen.first(&vec)).cloned().collect();
	    vec.pop();
	}

	return res;
    }
}

#[derive(Clone)]
pub struct State {
    pub items: Vec<Item>,
    pub item_to_id: HashMap<Item, usize>,
    pub nonterm_trans: HashMap<NonTerminal, usize>,
    pub term_trans: HashMap<Terminal, Action>,
}

impl PartialEq for State {
    fn eq(&self, other: &Self) -> bool {
        HashSet::<Item>::from_iter(self.items.iter().cloned())
	    == HashSet::<Item>::from_iter(other.items.iter().cloned())
    }
}
impl Eq for State { }

impl State {
    pub fn new(items: Vec<Item>, gen: &Generator) -> State {
	let mut state = State {
	    items: Vec::new(),
	    item_to_id: HashMap::new(),
	    nonterm_trans: HashMap::new(),
	    term_trans: HashMap::new()
	};

	for item in items.into_iter() {
	    state.add(item);
	}
	
	state.init(gen);
	
	return state;
    }

    // Make closure
    fn init(&mut self, gen: &Generator) {
	let mut changed_items: Vec<usize> = Vec::new();
	for i in 0..self.items.len() {
	    changed_items.push(i);
	}

	while !changed_items.is_empty() {
	    let i = changed_items.pop().unwrap();
	    let item = self.items[i].clone();
	    let las = item.get_la(gen);
	    if item.dot >= item.rule.right.len() {
		continue;
	    }
	    if let RightElem::NonTerm(nt) = &item.rule.right[item.dot] {
		for rule in find_rules(nt, &gen.gramma).into_iter() {
		    let nitem = Item::new(rule, 0, las.clone());
		    if let Some(id) = self.item_to_id.get(&nitem) {
			let mut cur_changed = false;
			for la in nitem.la.into_iter() {
			    cur_changed = self.items[*id].la.insert(la) || cur_changed;
			}
			if cur_changed {
			    changed_items.push(*id);
			}
		    } else {
			changed_items.push(self.add(nitem));
		    }
		}
	    }
	}
    }

    pub fn add(&mut self, item: Item) -> usize {
	let res = self.items.len();
	self.item_to_id.insert(item.clone(), self.items.len());
	self.items.push(item);
	return res;
    }
}

pub struct StateMachine {
    pub states: Vec<State>,
}

impl StateMachine {
    pub fn new(gen: &Generator) -> StateMachine {
	let mut st = StateMachine {
	    states: Vec::new(),
	};

	let init_item = Item::new(
	    find_rules(&gen.gramma.start, &gen.gramma)[0].clone(),
	    0,
	    HashSet::from_iter(vec![gen.gramma.end.clone()].into_iter()));
	let state = State::new(vec![init_item], gen);

	st.add(state.clone());

	st.init(gen);

	return st;
    }

    pub fn init(&mut self, gen: &Generator) {

	let mut changed_state: Vec<usize> = Vec::new();
	changed_state.push(0);

	while !changed_state.is_empty() {
	    let i = changed_state.pop().unwrap();
	    let state = self.states[i].clone();
	    for nt in gen.gramma.nonterms.iter() {
		let mut items = find_items(&RightElem::NonTerm(nt.clone()), &state);
		if items.is_empty() {
		    continue;
		}
		for item in items.iter_mut() {
		    item.dot += 1;
		}
		let nstate = State::new(items, gen);

		#[allow(unused_assignments)]
		let mut id = 0usize;
		if let Some(pid) = self.find_state(&nstate) {
		    if let Some(to) = state.nonterm_trans.get(&nt) {
			assert!(to == &pid, "Conflict transition by non terminal");
		    }
		    id = pid;

		    for item in nstate.items.iter() {
			let iid = self.states[id].item_to_id[&item];
			let mut cur_changed = false;
			for la in item.la.iter() {
			    cur_changed = self.states[id].items[iid].la.insert(la.clone()) || cur_changed;
			}
			if cur_changed {
			    changed_state.push(id);
			}
		    }
		} else {
		    id = self.add(nstate);
		    changed_state.push(id);
		}
		self.states[i].nonterm_trans.insert(nt.clone(), id);
	    }
	    for t in gen.gramma.terms.iter() {
		// Check conflicts
		let mut action: Option<Action> = None;
		for item in state.items.iter() {
		    let mut naction: Option<Action> = None;
		    if item.dot >= item.rule.right.len() && item.la.contains(&t) {
			naction = Some(Action::Reduce(item.rule.clone()));
		    } else if item.dot < item.rule.right.len() {
			if let RightElem::Term(rt) = &item.rule.right[item.dot] {
			    if rt == t {
				naction = Some(Action::Shift(0));
			    }
			}
		    }
		    if let Some(nact) = &naction {
			if let Some(act) = &action {
			    if let Err(msg) = act.check_conflic(&nact) {
				if msg == "shift-reduce coflict" {
				    naction = choose_shift_reduce(gen, t, &nact, &act);
				    if naction.is_none() {
					pwarning(
					    format!(
						"Cannot resolv shift reduce conflict for nonterminal {}\nConsider specify priority and assocativity",
						t.ident));
				    }
				} else {
				    perror(msg);
				    panic!("conflict");
				}
			    }
			}
			action = naction;
		    }
		}

		// Update transitions
		if let Some(action) = action {
		    match &action {
			Action::Reduce(_) => {
			    if let Some(act) = self.states[i].term_trans.get(&t) {
				if let Err(msg) = action.check_conflic(act) {
				    perror(format!("{}", msg));
				    panic!("conflic");
				}
			    } else {
				self.states[i].term_trans.insert(t.clone(), action);
			    }
			},
			&Action::Shift(_) => {
			    let mut items = find_items(&RightElem::Term(t.clone()), &state);
			    for item in items.iter_mut() {
				item.dot += 1;
			    }
			    let nstate = State::new(items, gen);

			    #[allow(unused_assignments)]
			    let mut id = 0usize;
			    if let Some(pid) = self.find_state(&nstate) {
				if let Some(act) = state.term_trans.get(&t) {
				    if let Err(msg) = Action::Shift(pid).check_conflic(act) {
					perror(format!("{}", msg));
					panic!("conflic");
				    }
				}
				id = pid;

				for item in nstate.items.iter() {
				    let iid = self.states[id].item_to_id[&item];
				    let mut cur_changed = false;
				    for la in item.la.iter() {
					cur_changed = self.states[id].items[iid].la.insert(la.clone()) || cur_changed;
				    }
				    if cur_changed {
					changed_state.push(id);
				    }
				}
			    } else {
				id = self.add(nstate);
				changed_state.push(id);
			    }
			    self.states[i].term_trans.insert(t.clone(), Action::Shift(id));
			}
		    }
		}
	    }
	}
    }

    fn find_state(&self, state: &State) -> Option<usize> {
	for i in 0..self.states.len() {
	    if &self.states[i] == state {
		return Some(i);
	    }
	}
	return None;
    }

    fn add(&mut self, state: State) -> usize {
	let id = self.states.len();
	self.states.push(state);
	return id;
    }

}

fn choose_shift_reduce(gen: &Generator, t: &Terminal, act1: &Action, act2: &Action) -> Option<Action> {
    let (shift, reduce) = if let &Action::Shift(_) = act1 {
	(act1, act2)
    } else {
	(act2, act1)
    };
    let mut res: Option<Action> = None;
    if let Some((assoc, prior)) = find_resolv(gen, t) {
	if let Action::Reduce(rule) = reduce {
	    if let Some(pr) = find_min_prior(gen, rule) {
		if pr > prior {
		    res = Some(shift.clone());
		} else if let Some(pr) = find_max_prior(gen, rule) {
		    if pr < prior {
			res = Some(reduce.clone());
		    }
		}
	    } 
	}
	if res.is_none() {
	    res = match assoc {
		Assoc::Left => Some(reduce.clone()),
		Assoc::Right => Some(shift.clone()),
	    }
	}
    }

    return res;
}

fn find_min_prior(gen: &Generator, rule: &Rule) -> Option<usize> {
    let mut res: Option<usize> = None;

    for r in rule.right.iter() {
	if let RightElem::Term(t) = r {
	    if let Some((_, prior)) = find_resolv(gen, &t) {
		if let Some(pr) = res {
		    res = Some(pr.max(prior));
		} else {
		    res = Some(prior);
		}
	    }
	}
    }
    return res;
}

fn find_max_prior(gen: &Generator, rule: &Rule) -> Option<usize> {
    let mut res: Option<usize> = None;

    for r in rule.right.iter() {
	if let RightElem::Term(t) = r {
	    if let Some((_, prior)) = find_resolv(gen, &t) {
		if let Some(pr) = res {
		    res = Some(pr.min(prior));
		} else {
		    res = Some(prior);
		}
	    }
	}
    }
    return res;
}

fn find_resolv(gen: &Generator, t: &Terminal) -> Option<(Assoc, usize)> {
    for r in gen.gramma.resolvs.iter() {
	if &r.0 == t {
	    return Some((r.1, r.2));
	}
    }
    return None;
}

fn find_items(r: &RightElem, state: &State) -> Vec<Item> {
    let mut res = Vec::new();
    for item in state.items.iter() {
	if item.dot < item.rule.right.len() && &item.rule.right[item.dot] == r {
	    res.push(item.clone());
	}
    }
    return res;
}

fn find_rules(nt: &NonTerminal, gramma: &Gramma) -> Vec<Rule> {
    let mut res = Vec::new();
    for rule in gramma.rules.iter() {
	if &rule.nonterm == nt {
	    res.push(rule.clone());
	}
    }
    return res;
}

pub fn print_state_machine(st: &StateMachine) {
    for (state, id) in st.states.iter().zip(0..) {
	println!("--------------------- State {} -----------------------------", id);
	print_state(state);
    }
}

fn print_item(item: &Item) {
    print!("  [");

    print_rule_with_dot(&item.rule, item.dot);

    print!(",");
    for la in item.la.iter() {
	print!(" {}", la.ident);
    }
    
    println!("]");
}

fn print_rule_with_dot(rule: &Rule, dot: usize) {
    print!("{}{}{} ->", color::Fg(color::LightBlue), rule.nonterm.ident, style::Reset);
    for (r, i) in rule.right.iter().zip(0..) {
	if i == dot {
	    print!(" {}{}·{}", color::Fg(color::Yellow), style::Bold, style::Reset);
	}
	print_right_elem(r);
    }
    if dot >= rule.right.len() {
	print!(" {}{}·{}", color::Fg(color::Yellow), style::Bold, style::Reset);
    }

    if rule.right.len() == 0 {
	print!(" ε");
    }
}

fn print_state(state: &State) {
    println!("Items:");
    for item in state.items.iter() {
	print_item(item);
    }
    println!("");
    println!("Non terminal transitions:");
    for (nt, id) in state.nonterm_trans.iter() {
	println!("  {}{}{}: {}", color::Fg(color::LightBlue), nt.ident, style::Reset, id);
    }
    println!("");
    println!("Terminal transitions:");
    for (t, act) in state.term_trans.iter() {
	match &act {
	    &Action::Reduce(rule) => {
		print!("  {}{}{}: Reduce(", color::Fg(color::LightBlue), t.ident, style::Reset);
		print_rule(rule);
		println!(")");
	    },
	    &Action::Shift(id) => {
		println!("  {}{}{}: Shift({})", color::Fg(color::LightBlue), t.ident, style::Reset, id);
	    }
	}
    }
}
