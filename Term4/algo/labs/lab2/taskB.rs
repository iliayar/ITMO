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


fn xorshift(n: i64) -> i64 {
    let mut x: i64 = n;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    if x < 0 { -x } else { x }
}

fn rand() -> i64 {
    xorshift(SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .subsec_nanos() as i64)
}

fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 {
	return a;
    } else {
	return gcd(b, a % b);
    }
}

fn modmul(a: i64, b: i64, m:i64) -> i64 {
    (((a as i128) * (b as i128)) % (m as i128)) as i64
}

fn pow(n: i64, k: i64, m: i64) -> i64 {
    if m == 0 {
	return 1;
    }
    let mut b: i64 = 1;
    let mut k = k;
    let mut n = n % m;
    while k > 1 {
	if k % 2 == 0 {
	    n = modmul(n, n, m);
	    k /= 2;
	} else {
	    b = modmul(b, n, m);
	    k -= 1;
	}
    }
    return modmul(b, n, m);
}

fn div2cnt(n: i64) -> (i64, i64) {
    let mut res = 0;
    let mut n = n;
    while n % 2 == 0 {
	res += 1;
	n /= 2;
    }
    return (res, n);
}

fn prime_test(n: i64) -> bool {
    if n == 1 {
	return false;
    }
    if n == 2 {
	return true;
    }
    for i in 0..10 {
	let a = xorshift(!i) % (n - 2) + 2;
	if gcd(a, n) != 1 {
	    return false;
	}
	let (c, mut y) = div2cnt(n - 1);
	let mut a = pow(a, y, n);
	let mut ok = true;
	for _ in 0..c {
	    if a != 1 {
		ok = a == n - 1;
	    }
	    a = modmul(a, a, n);
	}
	if(!ok) {
	    return false;
	}
    } 
    return true;
}

fn sol(scan: &mut Scanner, out: &mut dyn Write ) {
    let n = scan.next::<i64>();
    for _ in 0..n {
	let m = scan.next::<i64>();
	if prime_test(m) {
	    writeln!(out, "YES").ok();
	} else {
	    writeln!(out, "NO").ok();
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
