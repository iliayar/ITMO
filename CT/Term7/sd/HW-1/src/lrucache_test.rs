use crate::lrucache;

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::lrucache::*;

    #[rstest]
    #[case(
	10,
	vec![(10, 1), (20, 2), (30, 3)],
	vec![(10, true), (15, false), (20, true)],
	vec![(10, 1), (20, 2), (30, 3)],
    )]
    #[case(
	2,
	vec![(10, 1), (20, 2), (30, 3)],
	vec![(10, false), (15, false), (30, true), (20, true)],
	vec![(20, 2), (30, 3)],
    )]
    fn basic(
	#[case] max_size: usize,
	#[case] input: Vec<(usize, i32)>,
	#[case] assertions: Vec<(usize, bool)>,
	#[case] assert_values: Vec<(usize, i32)>,
    ) {
	let mut cache: LRUCache<usize, i32> = LRUCache::new(max_size).unwrap();

	for (addr, value) in input.iter() {
	    cache.put(addr, *value);
	}

	for (addr, exists) in assertions.iter() {
	    assert_eq!(cache.contains(addr), *exists);
	}

	for (addr, value) in assert_values.iter() {
	    assert_eq!(
		cache.get(addr)
		    .expect("Also check address in cache"),
		*value,
	    );
	}
    }

}
