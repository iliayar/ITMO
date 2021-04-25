#[allow(unused_imports)]
use std::cmp::{min,max};
use std::io::{BufWriter, stdin, stdout, Write};
 
#[derive(Default)]
struct Scanner {
    buffer: Vec<String>
}
impl Scanner {
    fn next<T: std::str::FromStr>(&mut self) -> T {
        loop {
            if let Some(token) = self.buffer.pop() {
                return token.parse().ok().expect("Failed parse");
            }
            let mut input = String::new();
            stdin().read_line(&mut input).expect("Failed read");
            self.buffer = input.split_whitespace().rev().map(String::from).collect();
        }
    }
}

// CODE_HERE

const MOD: i64 = 998_244_353;

fn normalize(n: &mut i64) {
    *n = (*n + MOD) % MOD;
}

fn sum(a: &[i64] , b: &[i64]) -> Vec<i64> {
    let mut p = Vec::new();
    p.resize(std::cmp::max(a.len(), b.len()), 0);
    for i in 0..p.len() {
	p[i] = if i >= a.len() {
	    0
	} else {
	    a[i]
	} + if i >= b.len() {
	    0
	} else {
	    b[i]
	};
	normalize(&mut p[i]);
    }
    return p;
}

fn mult(a: &[i64], b: &[i64]) -> Vec<i64> {
    let mut p = Vec::new();
    p.resize(a.len() + b.len() - 1, 0);
    for i in 0..a.len() {
	for j in 0..b.len() {
	    p[i + j] += a[i] * b[j];
	    normalize(&mut p[i + j]);
	}
    }
    return p;
}

fn divide(a: &[i64], b: &[i64], size: usize) -> Vec<i64> {
    let mut p = Vec::new();
    p.resize(size, 0);
    for i in 0..size {
	let mut sum: i64 = 0;
	for j in 0..i {
	    sum += p[j] * if i - j >= b.len() { 0 } else { b[i - j] };
	    normalize(&mut sum);
	}
	p[i] = ( if i >= a.len() { 0 } else { a[i] } - sum) / b[0] % MOD;
	normalize(&mut p[i]);
    }
    return p;
}

fn main() {
    let mut scan = Scanner::default();
    let out = &mut BufWriter::new(stdout());
    
    let n: usize = scan.next::<usize>();
    let m: usize = scan.next::<usize>();
    let p1: Vec<i64> =  (0..n+1).map(|_| scan.next()).collect();
    let p2: Vec<i64> =  (0..m+1).map(|_| scan.next()).collect();

    let p = sum(&p1, &p2);
    writeln!(out, "{}", p.len() - 1).ok();
    for e in p {
	write!(out, "{} ", e).ok();
    }
    writeln!(out, "").ok();
    let p = mult(&p1, &p2);
    writeln!(out, "{}", p.len() - 1).ok();
    for e in p {
	write!(out, "{} ", e).ok();
    }
    writeln!(out, "").ok();
    let p = divide(&p1, &p2, 1000);
    for e in p {
	write!(out, "{} ", e).ok();
    }
    writeln!(out, "").ok();
}
