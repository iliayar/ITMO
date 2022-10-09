use std::{collections::HashMap, hash::Hash};

use crate::linkedlist::{LinkedList, self};

pub struct LRUCache<Addr, Value> {
    map: HashMap<Addr, linkedlist::Elem<(Addr, Value)>>,
    list: LinkedList<(Addr, Value)>,
    max_size: usize,
}

impl<Addr, Value> LRUCache<Addr, Value>
where Addr: Eq + Hash + Clone
{
    pub fn new(max_size: usize) -> Option<Self> {
	if max_size == 0 {
	    return None;
	}

	let res = Self {
	    max_size,
	    map: HashMap::new(),
	    list: LinkedList::new(),
	};

	Some(res)
    }


    pub fn put(&mut self, addr: &Addr, value: Value) {
	if !self.map.contains_key(&addr) {
	    if self.map.len() >= self.max_size {
		let elem = self.list.peek()
		    .expect("List should not be empty, map size is greater than 0");

		self.map.remove(&elem.value().0);
		self.list.pop()
		    .expect("List is not empty");
	    }

	    let elem = self.list.push((addr.clone(), value));
	    self.map.insert(addr.clone(), elem);
	}

	assert!(self.map.len() <= self.max_size);
	assert!(self.map.contains_key(addr));
    }

    pub fn contains(&self, addr: &Addr) -> bool {
	self.map.contains_key(addr)
    }
}


impl<Addr, Value> LRUCache<Addr, Value>
where
    Addr: Eq + Hash + Clone,
    Value: Clone
{

    pub fn get(&self, addr: &Addr) -> Option<Value>
    {
	if self.map.contains_key(addr) {
	    let elem = self.map.get(addr)
		.expect("Key in the map");
	    Some(elem.value().1.clone())
	} else {
	    None
	}
    }
}
