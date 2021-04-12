#![allow(dead_code)]
#[allow(unused_imports)]
use std::cmp::{min,max};
use std::io::{BufWriter, stdin, stdout, Write, BufRead, BufReader};
use std::iter;
use std::ops;

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

const MOD: i64 = 104_857_601;

/// returns (g, x, y)
fn gcdext(a: i64, b: i64) -> (i64, i64, i64) {
    if a == 0 {
	return (b, 0, 1);
    }
    let (d, x, y) = gcdext(b % a, a);
    (d, y - (b / a) * x, x)
}

trait Numeric
{
    fn add(&self, rhs: &Self) -> Self;
    fn mul(&self, rhs: &Self) -> Self;
    fn div(&self, rhs: &Self) -> Self;
    fn from(n: i64) -> Self;
    fn display(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
    fn debug(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
    fn eq(&self, other: &Self) -> bool;
    fn one() -> Self;
    fn zero() -> Self;
}

#[derive(Clone,Copy)]
struct Num<T> {
    value: T
}

impl<T: Numeric> Num<T> {
    fn one() -> Self {
	Num { value: T::one() }
    }
    fn zero() -> Self {
	Num { value: T::zero() }
    }
}

impl<T> ops::Add<Num<T>> for Num<T>
where
    T: Numeric
{
    type Output = Num<T>;

    fn add(self, rhs: Num<T>) -> Self::Output {
        Num { value: self.value.add(&rhs.value) }
    }
}

impl<T: Numeric> ops::Add<&Num<T>> for &Num<T>
{
    type Output = Num<T>;

    fn add(self, rhs: &Num<T>) -> Self::Output {
        Num { value: self.value.add(&rhs.value) }
    }
}

impl<T: Numeric> ops::Mul<Num<T>> for Num<T> {
    type Output = Num<T>;

    fn mul(self, rhs: Num<T>) -> Self::Output {
        Num { value: self.value.mul(&rhs.value) }
    }
}

impl<T: Numeric> ops::Mul<&Num<T>> for &Num<T> {
    type Output = Num<T>;

    fn mul(self, rhs: &Num<T>) -> Self::Output {
        Num { value: self.value.mul(&rhs.value) }
    }
}

impl<T: Numeric> ops::Div<Num<T>> for Num<T> {
    type Output = Num<T>;

    fn div(self, rhs: Num<T>) -> Self::Output {
        Num { value: self.value.div(&rhs.value) }
    }
}

impl<T: Numeric> ops::Div<&Num<T>> for &Num<T> {
    type Output = Num<T>;

    fn div(self, rhs: &Num<T>) -> Self::Output {
        Num { value: self.value.div(&rhs.value) }
    }
}

impl<T: Numeric> ops::Sub<Num<T>> for Num<T> {
    type Output = Num<T>;

    fn sub(self, rhs: Num<T>) -> Self::Output {
        Num { value: self.value.add(&rhs.value.mul(&T::from(-1))) }
    }
}

impl<T: Numeric> ops::Sub<&Num<T>> for &Num<T> {
    type Output = Num<T>;

    fn sub(self, rhs: &Num<T>) -> Self::Output {
        Num { value: self.value.add(&rhs.value.mul(&T::from(-1))) }
    }
}

impl<T: Numeric> From<i32> for Num<T> {
    fn from(n: i32) -> Self {
        Num { value: T::from(n as i64) }
    }
}

impl<T: Numeric> From<i64> for Num<T> {
    fn from(n: i64) -> Self {
        Num { value: T::from(n) }
    }
}

impl<T: Numeric> From<usize> for Num<T> {
    fn from(n: usize) -> Self {
        Num { value: T::from(n as i64) }
    }
}

impl<T: Numeric> std::fmt::Display for Num<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value.display(f)
    }
}

impl<T: Numeric> std::fmt::Debug for Num<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value.debug(f)
    }
}

impl<T: Numeric> PartialEq for Num<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value.eq(&other.value)
    }
}

impl<T: Numeric> Eq for Num<T> { }

#[derive(Clone,Copy)]
struct Finite {
    value: u128,
    m: u128
}

impl Numeric for Finite {
    fn add(&self, rhs: &Self) -> Self {
	assert_eq!(self.m, rhs.m);
	Finite { value: (self.value + rhs.value) % self.m, m: self.m }
    }

    fn mul(&self, rhs: &Self) -> Self {
	assert_eq!(self.m, rhs.m);
	if self.value.checked_mul(rhs.value).is_none() {
	    // let n = self.value / 2;
	    // return rhs * Finite::from(n) + rhs * Finite::from(self.value - n); 
	}
        Finite { value: (self.value * rhs.value) % self.m, m: self.m }
    }

    fn div(&self, rhs: &Self) -> Self {
	assert_eq!(self.m, rhs.m);
        self.mul(&rhs.invert())
    }

    fn from(n: i64) -> Self {
	let mut value = n;
	while value < 0 {
	    value += MOD;
	}
	assert!(value >= 0, "Finite from i32 failed to produce positive number");
        Finite { value: (value % MOD) as u128, m: MOD as u128 }
    }
    
    fn display(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }

    fn debug(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }

    fn one() -> Self {
        Finite { value: 1, m: MOD as u128 }
    }

    fn zero() -> Self {
        Finite { value: 0, m: MOD as u128 }
    }
}
    
impl Finite {
    fn invert(&self) -> Finite {
	let (g, x, _) = gcdext(self.value as i64, MOD as i64);
	if g != 1 {
	    panic!("Should find inverted");
	} else {
	    Finite { value: x as u128, m: self.m }
	}
    }
}

impl Into<usize> for Finite {
    fn into(self) -> usize {
        self.value as usize
    }
}

fn comb<T>(n: usize, k: usize) -> Num<T>
where
    T: Numeric
{
    let mut res = Num::one();
    for i in (n - k + 1)..=n {
	res = res * Num::from(i);
    }
    for i in 1..=k {
	res = res / Num::from(i);
    }
    return res;
}

struct Polynom<T> {
    value: Vec<T>
}

impl<T: Numeric + Copy> Numeric for Polynom<Num<T>> {
    fn add(&self, rhs: &Self) -> Self {
	let a: &[Num<T>] = &self.value;
	let b: &[Num<T>] = &rhs.value;

	let mut p = vec![Num::zero(); max(a.len(), b.len())];
	for i in 0..p.len() {
	    p[i] = if i >= a.len() {
		Num::zero()
	    } else {
		a[i]
	    } + if i >= b.len() {
		Num::zero()
	    } else {
		b[i]
	    };
	}
	return Polynom { value: p };
    }

    fn mul(&self, rhs: &Self) -> Self {
	let a: &[Num<T>] = &self.value;
	let b: &[Num<T>] = &rhs.value;
	let mut p = vec![Num::zero(); a.len() + b.len() - 1];
	for i in 0..a.len() {
	    for j in 0..b.len() {
		p[i + j] = p[i + j] + a[i] * b[j];
	    }
	}
	return Polynom { value: p };
    }

    fn div(&self, rhs: &Self) -> Self {
        self.div(rhs, max(self.value.len(), rhs.value.len()))
    }

    fn from(n: i64) -> Self {
        Polynom { value: vec![Num::from(n as i32)] }
    }

    fn display(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for t in self.value.iter() {
	    write!(f, "{} ", t)?;
	}
	Ok(())
    }

    fn debug(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.display(f)
    }

    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }

    fn one() -> Self {
	Polynom { value: vec![Num::one()] }
    }

    fn zero() -> Self {
        Polynom { value: vec![] }
    }
}

impl<T, V> From<Vec<V>> for Num<Polynom<T>>
where T: From<V>,
      V: Copy
{
    fn from(p: Vec<V>) -> Self {
        return Num { value: Polynom { value: p.iter().map(|e| T::from(*e)).collect() } };
    }
}

impl<T> Polynom<Num<T>>
where
    T: Copy + Numeric
{
    fn div(&self, rhs: &Polynom<Num<T>>, size: usize) -> Polynom<Num<T>> {
	let a: &[Num<T>] = &self.value;
	let b: &[Num<T>] = &rhs.value;
	let mut p = vec![Num::zero(); size];
	for i in 0..p.len() {
	    let mut sum = Num::zero();
	    for j in 0..i {
		sum = sum + p[j] * if i - j >= b.len() { Num::zero() } else { b[i - j] };
	    }
	    p[i] = (if i >= a.len() { Num::zero() } else { a[i] } + Num::from(-1)*sum) / b[0];
	}
	let res = Polynom { value: p };
	return res;
    }
    fn from_recursive(a: &[Num<T>], c: &[Num<T>]) -> (Num<Polynom<Num<T>>>, Num<Polynom<Num<T>>>) {
	let mut p: Vec<Num<T>> = a.iter().cloned().collect();
	let mut last_nonz: usize = 0;
	for i in 0..c.len() {
	    for j in 0..min(c.len(), i) {
		p[i] = p[i] + Num::from(-1) * a[i - j - 1]*c[j];
	    }
	    if p[i] != Num::from(0) {
		last_nonz = i;
	    }
	}
	p.resize(last_nonz + 1, Num::zero());
	let q: Vec<Num<T>> = iter::once(Num::one()).into_iter().chain(c.iter().map(|e| e*&Num::from(-1))).collect();
	return (Num { value: Polynom { value: p } }, Num { value: Polynom { value: q } });
    }

    fn negate_arg(&self) -> Polynom<Num<T>> {
	let mut res = vec![Num::from(0); self.value.len()];
	for i in 0..self.value.len() {
	    res[i] = if i % 2 == 0 {
		self.value[i]
	    } else {
		Num::from(-1) * self.value[i]
	    };
	}
	return Polynom { value: res };
    }
}

fn sol(scan: &mut Scanner, out: &mut dyn Write ) {


    let k = scan.next::<usize>();
    let mut n = scan.next::<usize>() - 1;

    let a: Vec<Num<Finite>> = (0..k).map(|_| Num::from(scan.next::<i64>())).collect();
    let c: Vec<Num<Finite>> = (0..k).map(|_| Num::from(scan.next::<i64>())).collect();

    let (mut p, mut q) = Polynom::from_recursive(&a[..], &c[..]);
    // p = From::from(a);
    println!("DBG: p = {}", p);
    println!("DBG: q = {}", q);

    while n >= k {
	println!("===========================");
	let nq = Num { value: q.value.negate_arg() };
	p = &nq * &p;
	q = &nq * &q;
	println!("DBG: p = {}", p);
	println!("DBG: q = {}", q);

	let mut nqv = vec![Num::from(0); (q.value.value.len() + 1)/2];
	let mut npv = vec![Num::from(0); k];
	for i in 0..nqv.len() {
	    nqv[i] = q.value.value[i * 2];
	}
	for i in (n % 2)..k {
	    npv[i] = p.value.value[i * 2];
	}
	n /= 2;
	p = From::from(npv);
	q = From::from(nqv);
	println!("DBG: p = {}", p);
	println!("DBG: q = {}", q);
    }

    writeln!(out, "{}", p.value.value[n]).ok();
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
