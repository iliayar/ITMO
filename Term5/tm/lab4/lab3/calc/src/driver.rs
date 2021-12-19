use std::collections::HashMap;

pub struct CalcDriver {
    vars: HashMap<String, i64>,
}

impl CalcDriver {
    pub fn new() -> Self {
	Self {
	    vars: HashMap::new(),
	}
    }

    pub fn set(&mut self, var: String, value: i64) {
	println!("{} = {}", var, value);
	self.vars.insert(var, value);
    }

    pub fn get(&mut self, var: String) -> i64 {
	return self.vars[&var];
    }

    pub fn eval(&self, value: i64) {
	println!("{}", value);
    }
}
