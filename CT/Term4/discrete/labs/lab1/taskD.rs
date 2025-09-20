#![allow(dead_code)]
#[allow(unused_imports)]
use std::cmp::{min,max};
use std::io::{BufWriter, stdin, stdout, Write};
use std::iter;
use std::ops;

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

const MOD: i128 = 998_244_353;

fn normalize(n: &mut i128) {
    *n = (*n % MOD + MOD) % MOD;
}

/// A(t) + B(t)
fn sum(a: &[i128] , b: &[i128]) -> Vec<i128> {
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
fn mult(a: &[i128], b: &[i128]) -> Vec<i128> {
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
fn divide(a: &[i128], b: &[i128], size: usize) -> Vec<i128> {
    let mut p = vec![0; size];
    for i in 0..size {
	let mut sum: i128 = 0;
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
fn subs(a: &[i128], b: &[i128]) -> Vec<i128> {
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
fn gcdext(a: i128, b: i128) -> (i128, i128, i128) {
    if a == 0 {
	return (b, 0, 1);
    }
    let (d, x, y) = gcdext(b % a, a);
    (d, y - (b / a) * x, x)
}

fn invert(n: i128) -> i128 {
    let (g, mut x, _) = gcdext(n, MOD);
    if g != 1 {
	panic!("Should find inverted");
    } else {
	normalize(&mut x);
	x
    }
}

fn gen_exp(size: usize) -> Vec<i128> {
    let mut p = vec![0; size];
    let mut fact = 1;
    for i in 0..size {
	let n = i as i128;
	p[i] = invert(fact);
	fact *= n + 1;
	normalize(&mut fact);
    }
    return p;
}

fn gen_sqrt(size: usize) -> Vec<i128> {
    let mut p = vec![0; size];
    let mut fact1: i128 = 1;
    let mut fact2: i128 = 1;
    let mut pow: i128 = 1;
    for i in 0..size {
	let n = i as i128;
	let mut sign = if n % 2 == 0 { 1 } else { -1 };
	p[i] = fact2;
	normalize(&mut p[i]);
	let mut t: i128 = 1 - 2*n;
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

fn gen_ln(size: usize) -> Vec<i128> {
    let mut p = vec![0; size];
    p[0] = 0;
    for i in 1..size {
	let n = i as i128;
	p[i] = invert(n);
	p[i] *= if n % 2 == 0 { -1 } else { 1 };
	normalize(&mut p[i])
    }
    return p;
}

fn gen_from_recursive(a: &[i128], c: &[i128]) -> (Vec<i128>, Vec<i128>) {
    
    let mut p: Vec<i128> = a.iter().cloned().collect();
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
    let q: Vec<i128> = iter::once(1).into_iter().chain(c.iter().map(|e| -e)).collect();
    return (p, q);
}

#[derive(Clone,Copy)]
struct Rational {
    denominator: i128,
    numerator: i128
}

impl Rational {
    fn new(numerator: i128, denominator: i128) -> Rational {
	let numer = if denominator < 0 { -numerator } else { numerator };
	let denom = if denominator < 0 { -denominator } else { denominator };
	let d = gcdext(if numer < 0 { -numer } else { numer }, denom).0;
	Rational {
	    denominator: denom / d,
	    numerator: numer / d,
	}
    }
}

impl std::fmt::Display for Rational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}/{}", self.numerator, self.denominator)
    }
}

impl ops::Add<Rational> for Rational {
    type Output = Rational;

    fn add(self, rhs: Rational) -> Rational {
	let mlt: i128 = gcdext(self.denominator, rhs.denominator).0;
	let denom: i128 = self.denominator * rhs.denominator / mlt;
	let numer = self.numerator * (denom / self.denominator) + rhs.numerator * (denom / rhs.denominator);
	Rational::new(numer, denom)
    }
}

impl ops::Mul<Rational> for Rational {
    type Output = Rational;

    fn mul(self, rhs: Rational) -> Self::Output {
        let denom = self.denominator * rhs.denominator;
	let numer = self.numerator * rhs.numerator;
	Rational::new(numer, denom)
    }
}

impl ops::Mul<i128> for Rational {
    type Output = Rational;

    fn mul(self, rhs: i128) -> Self::Output {
	self * Rational::new(rhs, 1)
    }
}

impl ops::Div<i128> for Rational {
    type Output = Rational;

    fn div(self, rhs: i128) -> Self::Output {
        self * Rational::new(1, rhs)
    }
}

impl ops::Add<i128> for Rational {
    type Output = Rational;

    fn add(self, rhs: i128) -> Self::Output {
        self + Rational::new(rhs, 1)
    }
}

impl From<i128> for Rational {
    fn from(numer: i128) -> Self {
        Rational::new(numer, 1)
    }
}

fn add_rational(a: &[Rational], b: &[Rational]) -> Vec<Rational> {
    let n = max(a.len(), b.len());
    let mut res = vec![Rational::from(0); n];
    for i in 0..n {
	res[i] = res[i] + if i < a.len() { a[i] } else { Rational::from(0) }
	+ if i < b.len() { b[i] } else { Rational::from(0) };
    }
    return res;
}
fn mult_rational(a: &[Rational], b: &[Rational]) -> Vec<Rational> {
    let mut p = vec![Rational::from(0); a.len() + b.len() - 1];
    for i in 0..a.len() {
	for j in 0..b.len() {
	    p[i + j] = p[i + j] + a[i] * b[j];
	}
    }
    return p;
}
    
fn to_quazi(k: usize, r: i128, p: &[Rational]) -> Vec<Rational> {
    let mut res = Vec::new();
    let mut fact: i128 = 1;
    for i in 1..(k + 1) {
	fact *= i as i128;
    }
    let mut pow = 1;
    for n in 0..p.len() {
	let mut pp =  vec![Rational::from(1)];
	for i in 1..(k + 1) {
	    pp = mult_rational(&pp, &vec![Rational::from((i as i128) - (n as i128)), Rational::from(1)]);
	}
	pp = pp.iter().map(|e| *e * p[n] / pow / fact).collect();
	res = add_rational(&res, &pp);
	pow *= r;
    }
    return res;
}


fn main() {
    let mut scan = Scanner::default();
    let out = &mut BufWriter::new(stdout());
    
    let r: i128 = scan.next::<i128>();
    let k: usize = scan.next::<usize>();
    let p: Vec<i128> =  (0..(k + 1)).map(|_| scan.next()).collect();

    let mut pr: Vec<Rational> = vec![Rational::from(0); k + 1];
    for i in 0..(k + 1) {
	pr[i] = Rational::from(p[i]);
    }

    let res = to_quazi(k, r, &pr);
    for r in res {
	write!(out, "{} ", r).ok();
    }
    writeln!(out, "").ok();
}
