#![allow(dead_code)]
#[allow(unused_imports)]
use std::cmp::{min,max};
use std::io::{BufWriter, stdin, stdout, Write, BufRead, BufReader};
use std::iter;
use std::ops;
use std::time::{SystemTime, UNIX_EPOCH};

const FILENAME: &str = "filename";
const IS_FILES: bool = false;

struct Scanner {
    buffer: Vec<String>,
    reader: Box<dyn BufRead>
}
impl Scanner {
    fn next<T: std::str::FromStr>(&mut self) -> T {
        loop {
            if let Some(token) = self.buffer.pop() {
                return token.parse().ok().expect("Failed parse");
            }
            let mut input = String::new();
            self.reader.read_line(&mut input).expect("Failed read");
            self.buffer = input.split_whitespace().rev().map(String::from).collect();
        }
    }

    fn new(reader: Box<dyn BufRead>) -> Scanner {
        Scanner {
            buffer: vec![],
            reader
        }
    }
}

//================================ CODE BEGIN ===============================================


fn gcdext(a: i64, b: i64) -> (i64, i64, i64) {
    if a == 0 {
	return (b, 0, 1);
    }
    let (d, x, y) = gcdext(b % a, a);
    (d, y - (b / a) * x, x)
}

fn solve_eq(a: i64, b: i64, c: i64) -> Option<(i64, i64)> {
    let (mut d, x, y) = gcdext(a, b);
    if c % d != 0 {
	return None;
    }
    return Some((x * (c / d), y * (c / d)));
}

fn sol(scan: &mut Scanner, out: &mut dyn Write ) {
    let mut a = scan.next::<i64>();
    let mut b = scan.next::<i64>();
    let mut n = scan.next::<i64>();
    let mut m = scan.next::<i64>();
    // let (a1, b1, c1) = (-m, n, b - a);
    // if let Some((x, y)) = solve_eq(a1, b1, c1) {
    // 	// println!("{}⋅x + {}⋅y = {} ⇔ x = {}, y = {}", a1, b1, c1, x, y);
    // 	assert_eq!(a + y*n, b + x*m);
    // 	writeln!(out, "{}", (a + y*n + m*n) % (m * n)).ok();
    // } else {
    // 	unreachable!("Hmmm....");
    // }
    if n < m {
	std::mem::swap(&mut a, &mut b);
	std::mem::swap(&mut n, &mut m);
    }
    for y in 0..n {
	let x = a + y * n;
	if x % m == b {
	    writeln!(out, "{}", x).ok();
	    return;
	}
    }
}

//================================ CODE END =================================================

fn main() {

    let mut local = false;
    for arg in std::env::args() {
        if arg == "LOCAL" {
            local = true;
        }
    }
    if local {
        let mut scan = Scanner::new(Box::new(BufReader::new(std::fs::File::open("local.in").expect("Cannot open local.in"))));
        let mut out = &mut BufWriter::new(std::fs::File::create("local.out").expect("Cannot open local.out"));
        let now = std::time::Instant::now();
        sol(&mut scan, &mut out);
        writeln!(out, "{}ms", now.elapsed().as_millis()).ok();
    } else {
        if IS_FILES {
            let mut scan = Scanner::new(Box::new(BufReader::new(std::fs::File::open(FILENAME.to_owned() + ".in").expect("Cannot open remote input"))));
            let mut out = &mut BufWriter::new(std::fs::File::create(FILENAME.to_owned() + ".out").expect("Cannot open remote output"));
            sol(&mut scan, &mut out);
        } else {
            let mut scan = Scanner::new(Box::new(BufReader::new(stdin())));
            let mut out = &mut BufWriter::new(stdout());
            sol(&mut scan, &mut out);
        }
    }
}
