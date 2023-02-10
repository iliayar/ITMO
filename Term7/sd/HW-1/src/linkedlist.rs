use std::{cell::RefCell, rc::Rc};
use std::error::Error;


pub struct LinkedListError {
    msg: String
}

impl LinkedListError {
    fn new(msg: String) -> Self {
	Self {
	    msg
	}
    }
}

impl Error for LinkedListError {
}

impl std::fmt::Display for LinkedListError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LinkedListError: {}", self.msg)
    }
}

impl std::fmt::Debug for LinkedListError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LinkedListError").field("msg", &self.msg).finish()
    }
}


type Ref<T> = Rc<RefCell<Node<T>>>;

pub struct Elem<T> {
    node: Ref<T>,
}

impl<T> Clone for Elem<T> {
    fn clone(&self) -> Self {
        Elem::<T>::new(self.node.clone())
    }
}

struct Node<T> {
    value: T,
    next: Option<Elem<T>>,
    prev: Option<Elem<T>>,
}

pub struct LinkedList<T> {
    begin: Option<Elem<T>>,
    end: Option<Elem<T>>,
}

impl<T> Node<T> {
    fn new(
	value: T,
    ) -> Ref<T> {
	let res = Self {
	    value,
	    next: None,
	    prev: None,
	};

	return Rc::new(RefCell::new(res));
    }
}

impl<T> Elem<T> {
    fn new(
	node: Ref<T>,
    ) -> Self {
	Self {
	    node
	}
    }

    fn new_linked(
	node: Ref<T>,
	next: Option<Elem<T>>,
	prev: Option<Elem<T>>,
    ) -> Self {
	let mut res = Elem::<T>::new(node);

	if let Some(elem) = next {
	    res.link_next(elem);
	}

	if let Some(elem) = prev {
	    res.link_prev(elem);
	}

	return res;
    }

    pub fn value(&self) -> std::cell::Ref<T> {
	std::cell::Ref::map(self.node.as_ref().borrow(), |node| &node.value)
    }

    fn get_node(&mut self) -> std::cell::RefMut<Node<T>> {
	self.node.as_ref().borrow_mut()
    }

    fn get_node_immut(&self) -> std::cell::Ref<Node<T>> {
	self.node.as_ref().borrow()
    }

    fn link_next(&mut self, mut next: Elem<T>) {
	assert!(self.get_node().prev.is_none(), "Trying overwrite existing next edge");
	assert!(next.get_node().prev.is_none(), "Trying link already linked next node");

	self.get_node().next = Some(next.clone());
	next.get_node().prev = Some(self.clone());
    }

    fn link_prev(&mut self, mut prev: Elem<T>) {
	assert!(self.get_node().prev.is_none(), "Trying overwrite existing prev edge");
	assert!(prev.get_node().next.is_none(), "Trying link already linked prev node");

	self.get_node().prev = Some(prev.clone());
	prev.get_node().next = Some(self.clone());
    }

    fn unlink_prev(&mut self) {
	if let Some(prev_elem) = self.get_node().prev.as_mut() {
	    prev_elem.get_node().next = None;
	} else {
	    assert!(false, "Trying to unlink not existing prev edge");
	}

	self.get_node().prev = None;
    }

    fn unlink_next(&mut self) {
	if let Some(next_elem) = self.get_node().next.as_mut() {
	    next_elem.get_node().prev = None;
	} else {
	    assert!(false, "Trying to unlink not existing next edge");
	}

	self.get_node().next = None;
    }

    fn erase(&mut self) {
	let node = self.get_node();
	let prev = node.prev.clone();
	let next = node.next.clone();
	drop(node);

	match (prev, next) {
	    (Some(mut prev_elem), Some(next_elem)) => {
		self.unlink_next();
		self.unlink_prev();
		prev_elem.link_next(next_elem);
	    },
	    (None, None) => {},
	    (None, Some(_)) => {
		self.unlink_next();
	    },
	    (Some(_), None) => {
		self.unlink_prev();
	    },
	};

	assert!(self.get_node().next.is_none());
	assert!(self.get_node().prev.is_none());
    }
}

impl<T> LinkedList<T> {
    pub fn new() -> Self {
	Self {
	    begin: Option::None,
	    end: Option::None,
	}
    }

    fn erase_impl(&mut self, elem: &mut Elem<T>) {
	let node = elem.get_node();
	match (&node.prev, &node.next) {
	    (None, None) => {
		self.begin = None;
		self.end = None;
	    },
	    (None, Some(next_elem)) => {
		self.begin = Some(next_elem.clone());
	    },
	    (Some(prev_elem), None) => {
		self.end = Some(prev_elem.clone());
	    },
	    (Some(_), Some(_)) => {},
	}

	drop(node);
	elem.erase();
    }

    pub fn erase(&mut self, mut elem: Elem<T>)  {
	self.erase_impl(&mut elem);

	self.check_invariant();
    }

    pub fn push(&mut self, value: T) -> Elem<T> {
	let elem = Elem::new_linked(Node::new(value), None, None);

	match (&mut self.begin, &mut self.end) {
	    (None, None) => {
		self.begin = Some(elem.clone());
		self.end = Some(elem.clone());
	    },
	    (Some(begin_elem), Some(_)) => {
		begin_elem.link_prev(elem.clone());
		self.begin = Some(elem.clone())
	    },
	    _ => assert!(false, "Inconsistent list, begin and end is not together None or Some"),
	}

	self.check_invariant();
	return elem;
    }

    pub fn pop(&mut self) -> Result<(), LinkedListError> {
	match (&self.begin, self.end.clone()) {
	    (Some(_), Some(mut end)) => {
		self.erase_impl(&mut end);
	    },
	    (None, None) => {
		return Result::Err(LinkedListError::new("Trying pop from empty list".to_owned()))
	    },
	    _ => assert!(false, "Inconsistent list, begin and end is not together None or Some"),
	};

	self.check_invariant();
	Ok(())
    }

    pub fn peek(&self) -> Result<Elem<T>, LinkedListError> {
	if let Some(end_elem) = &self.end {
	    Ok(end_elem.clone())
	} else {
	    Err(LinkedListError::new("Cannot peek element from empty list".to_owned()))
	}
    }

    fn check_invariant(&self) {
	match (&self.begin, &self.end) {
	    (Some(begin), Some(end)) => {
		assert!(begin.get_node_immut().prev.is_none(), "Begin has precessor");
		assert!(end.get_node_immut().next.is_none(), "End has successor");
	    },
	    (None, None) => {},
	    _ => assert!(false, "Inconsistent list, begin and end is not together None or Some"),
	};
    }
}
