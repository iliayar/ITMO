#![allow(dead_code)]
#[allow(unused_imports)]
use std::cmp::{min,max};
use std::io::{BufWriter, stdin, stdout, Write};
use std::iter;

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
    *n = (*n % MOD + MOD) % MOD;
}

/// A(t) + B(t)
fn sum(a: &[i64] , b: &[i64]) -> Vec<i64> {
    let mut p = vec![0; std::cmp::max(a.len(), b.len())];
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

/// A(t) * B(t)
fn mult(a: &[i64], b: &[i64]) -> Vec<i64> {
    let mut p = vec![0; a.len() + b.len() - 1];
    for i in 0..a.len() {
	for j in 0..b.len() {
	    p[i + j] += a[i] * b[j] % MOD;
	    normalize(&mut p[i + j]);
	}
    }
    return p;
}

/// A(t) / B(t)
/// @param a A(t)
/// @param b B(t)
fn divide(a: &[i64], b: &[i64], size: usize) -> Vec<i64> {
    let mut p = vec![0; size];
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

/// A(B(t))
fn subs(a: &[i64], b: &[i64]) -> Vec<i64> {
    let size = (a.len() - 1)*(b.len() - 1) + 1;
    let mut p = vec![0; size];
    let mut bn = vec![0; size + b.len()];
    let mut bnt = vec![0; size + b.len()];
    let mut l = b.len();
    bn[0..b.len()].copy_from_slice(b);
    p[0] = a[0];
    for i in 1..a.len() {
	for j in i..l {
	    p[j] += a[i] * bn[j] % MOD;
	    normalize(&mut p[j]);
	}

	let bnt = &mut bnt[(i - 1)..l];
	let bn = &mut bn[i..(l + b.len())];
	for j in 0 .. bnt.len() {
	    bnt[j] = bn[j];
	}
	for j in 0..bn.len() {
	    bn[j] = 0;
	}
	for j in 0..bnt.len() {
	    for k in 0..b.len() {
		bn[k + j] += bnt[j] * b[k] % MOD;
		normalize(&mut bn[k + j]);
	    }
	}
	
	l += b.len() - 1;
    }
    return p;
}

/// returns (g, x, y)
fn gcdext(a: i64, b: i64) -> (i64, i64, i64) {
    if a == 0 {
	return (b, 0, 1);
    }
    let (d, x, y) = gcdext(b % a, a);
    (d, y - (b / a) * x, x)
}

fn invert(n: i64) -> i64 {
    let (g, mut x, _) = gcdext(n, MOD);
    if g != 1 {
	panic!("Should find inverted");
    } else {
	normalize(&mut x);
	x
    }
}

fn gen_exp(size: usize) -> Vec<i64> {
    let mut p = vec![0; size];
    let mut fact = 1;
    for i in 0..size {
	let n = i as i64;
	p[i] = invert(fact);
	fact *= n + 1;
	normalize(&mut fact);
    }
    return p;
}

fn gen_sqrt(size: usize) -> Vec<i64> {
    let mut p = vec![0; size];
    let mut fact1: i64 = 1;
    let mut fact2: i64 = 1;
    let mut pow: i64 = 1;
    for i in 0..size {
	let n = i as i64;
	let mut sign = if n % 2 == 0 { 1 } else { -1 };
	p[i] = fact2;
	normalize(&mut p[i]);
	let mut t: i64 = 1 - 2*n;
	if t < 0 {
	    t *= -1;
	    sign *= -1;
	}
	t *= fact1 * fact1 % MOD;
	normalize(&mut t);
	t *= pow;
	normalize(&mut t);
	p[i] *= invert(t) * sign % MOD;
	normalize(&mut p[i]);

	fact2 *= (2*n + 1) * (2*n + 2) % MOD;
	normalize(&mut fact2);
	fact1 *= n + 1;
	normalize(&mut fact1);
	pow *= 4;
	normalize(&mut pow);
    }
    return p;
}

fn gen_ln(size: usize) -> Vec<i64> {
    let mut p = vec![0; size];
    p[0] = 0;
    for i in 1..size {
	let n = i as i64;
	p[i] = invert(n);
	p[i] *= if n % 2 == 0 { -1 } else { 1 };
	normalize(&mut p[i])
    }
    return p;
}

fn gen_from_recursive(a: &[i64], c: &[i64]) -> (Vec<i64>, Vec<i64>) {
    
    let mut p: Vec<i64> = a.iter().cloned().collect();
    let mut last_nonz: usize = 0;
    for i in 0..c.len() {
	for j in 0..min(c.len(), i) {
	    p[i] -= a[i - j - 1]*c[j];
	}
	if p[i] != 0 {
	    last_nonz = i;
	}
    }
    p.resize(last_nonz + 1, 0);
    let q: Vec<i64> = iter::once(1).into_iter().chain(c.iter().map(|e| -e)).collect();
    return (p, q);
}

fn main() {
    let mut scan = Scanner::default();
    let out = &mut BufWriter::new(stdout());
    
    let k: usize = scan.next::<usize>();
    let a: Vec<i64> =  (0..k).map(|_| scan.next()).collect();
    let c: Vec<i64> =  (0..k).map(|_| scan.next()).collect();
    
    let (p, q) = gen_from_recursive(&a, &c);
    writeln!(out, "{}", p.len() - 1).ok();
    for e in p {
	write!(out, "{} ", e).ok();
    }
    writeln!(out, "").ok();
    writeln!(out, "{}", q.len() - 1).ok();
    for e in q {
	write!(out, "{} ", e).ok();
    }
    writeln!(out, "").ok();
    
}
