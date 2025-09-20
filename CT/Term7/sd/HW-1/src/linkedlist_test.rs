use super::linkedlist;

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::linkedlist::*;

    #[rstest]
    #[case(vec![42])]
    #[case(vec![1, 2, 3])]
    #[case(vec![4, 10, 23, 512])]
    fn push_pop(#[case] input: Vec<i32>) {
	let mut list = LinkedList::<i32>::new();

	for i in input.iter() {
	    list.push(*i);
	}

	for i in input.iter() {
	    assert_eq!(list.peek().unwrap().value().clone(), *i);
	    list.pop().ok();
	}
    }


    #[rstest]
    #[case(vec![1, 2, 3], 1)]
    #[case(vec![1], 0)]
    #[case(vec![1, 2], 0)]
    #[case(vec![1, 2], 1)]
    fn erase_elem(#[case] input: Vec<i32>, #[case] idx: usize) {
	let mut list = LinkedList::<i32>::new();

	let mut elem_to_remove: Option<Elem<i32>> = None;

	for (i, n) in input.iter().enumerate() {
	    let elem = list.push(*n);

	    if i == idx {
		elem_to_remove = Some(elem);
	    }
	}

	let elem_to_remove_value = elem_to_remove.as_ref().unwrap().value().clone();
	list.erase(elem_to_remove.unwrap());

	for (i, n) in input.iter().enumerate() {
	    if i != idx {
		assert_eq!(list.peek().unwrap().value().clone(), *n);
		list.pop().ok();
	    } else {
		assert_eq!(elem_to_remove_value, *n);
	    }
	}
    }

}
