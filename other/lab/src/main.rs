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

const MOD: i64 =  998_244_353;

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

// #[derive(Clone,Copy)]
// struct Rational {
//     denominator: i64,
//     numerator: i64
// }

// impl PartialEq for Rational {
//     fn eq(&self, other: &Self) -> bool {
//         return self.numerator == other.numerator && self.denominator == other.denominator;
//     }
// }

// impl Eq for Rational {}

// impl Rational {
//     fn new(numerator: i64, denominator: i64) -> Rational {
// 	let numer = if denominator < 0 { -numerator } else { numerator };
// 	let denom = if denominator < 0 { -denominator } else { denominator };
// 	let d = gcdext(if numer < 0 { -numer } else { numer }, denom).0;
// 	Rational {
// 	    denominator: denom / d,
// 	    numerator: numer / d,
// 	}
//     }
// }

// impl Into<usize> for Rational {
//     fn into(self) -> usize {
//         self.numerator as usize
//     }
// }

// impl std::fmt::Display for Rational {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         write!(f, "{}/{}", self.numerator, self.denominator)
//     }
// }

// impl ops::Add<Rational> for Rational {
//     type Output = Rational;

//     fn add(self, rhs: Rational) -> Rational {
// 	let mlt: i64 = gcdext(self.denominator, rhs.denominator).0;
// 	let denom: i64 = self.denominator * rhs.denominator / mlt;
// 	let numer = self.numerator * (denom / self.denominator) + rhs.numerator * (denom / rhs.denominator);
// 	Rational::new(numer, denom)
//     }
// }

// impl ops::Mul<Rational> for Rational {
//     type Output = Rational;

//     fn mul(self, rhs: Rational) -> Self::Output {
//         let denom = self.denominator * rhs.denominator;
// 	let numer = self.numerator * rhs.numerator;
// 	Rational::new(numer, denom)
//     }
// }

// impl ops::Div<Rational> for Rational {
//     type Output = Rational;

//     fn div(self, rhs: Rational) -> Self::Output {
//         return self * Rational::new(rhs.denominator, rhs.numerator);
//     }
// }

// impl From<i64> for Rational {
//     fn from(numer: i64) -> Self {
//         Rational::new(numer, 1)
//     }
// }

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

    fn subs(&self, arg: &Polynom<Num<T>>) -> Polynom<Num<T>> {
	let a: &[Num<T>] = &self.value;
	let b: &[Num<T>] = &arg.value;
	let size = (a.len() - 1)*(b.len() - 1) + 1;
	let mut p = vec![Num::zero(); size];
	let mut bn = vec![Num::zero(); size + b.len()];
	let mut bnt = vec![Num::zero(); size + b.len()];
	let mut l = b.len();
	bn[0..b.len()].copy_from_slice(b);
	p[0] = a[0];
	for i in 1..a.len() {
	    for j in i..l {
		p[j] = p[j] + a[i] * bn[j];
	    }

	    let bnt = &mut bnt[(i - 1)..l];
	    let bn = &mut bn[i..(l + b.len())];
	    for j in 0 .. bnt.len() {
		bnt[j] = bn[j];
	    }
	    for j in 0..bn.len() {
		bn[j] = Num::zero();
	    }
	    for j in 0..bnt.len() {
		for k in 0..b.len() {
		    bn[k + j] = bn[k + j] + bnt[j] * b[k];
		}
	    }
	    
	    l += b.len() - 1;
	}
	return Polynom { value: p };

    }

    fn exp(size: usize) -> Polynom<Num<T>> {
	let mut p = vec![Num::zero(); size];
	let mut fact = Num::one();
	for i in 0..size {
	    let n = Num::from(i);
	    p[i] = Num::one() / fact;
	    fact = fact * (n + Num::one());
	}
	return Polynom { value: p };
    }

    fn sqrt(size: usize) -> Polynom<Num<T>> {
	let mut p = vec![Num::zero(); size];
	let mut fact1 = Num::one();
	let mut fact2 = Num::one();
	let mut pow = Num::one();
	for i in 0..size {
	    let n = Num::from(i);
	    let sign = if i % 2 == 0 { 1 } else { -1 };
	    p[i] = fact2;
	    let mut t = Num::from(1) + Num::from(-2)*n;
	    t = Num::from(sign) * t * fact1 * fact1 * pow;
	    p[i] = p[i] / t;
	    fact2 = fact2 * (Num::from(2)*n + Num::from(1)) * (Num::from(2)*n + Num::from(2));
	    fact1 = fact1 * (n + Num::from(1));
	    pow = pow * Num::from(4);
	}
	return Polynom { value: p };
    }

    fn ln(size: usize) -> Polynom<Num<T>> {
	let mut p = vec![Num::zero(); size];
	for i in 1..size {
	    let n = Num::from(i);
	    p[i] = Num::one() / n;
	    let sign = if i % 2 == 0 { -1 } else { 1 };
	    p[i] = p[i] * Num::from(sign);
	}
	return Polynom { value: p };
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

    fn to_quazi(self, k: usize, r: Num<T>) -> Vec<Num<T>> {
	let mut res: Num<Polynom<Num<T>>> = Num::zero();
	let mut fact = Num::one();
	for i in 1..(k + 1) {
	    fact = fact * Num::from(i);
	}
	let mut pow = Num::from(1);
	for n in 0..self.value.len() {
	    let mut pp: Num<Polynom<Num<T>>> = From::from(vec![1]);
	    for i in 1..(k + 1) {
		let t = From::from(vec![(i as i32) - (n as i32), 1]);
		pp = pp * t;
	    }
	    pp = Num { value: Polynom { value: pp.value.value.iter().map(|e| *e * self.value[n] / pow / fact).collect() } };
	    res = res + pp;
	    pow = pow * r;
	}
	return res.value.value;
    }

//     fn from_quazi(r: T, d: usize, p: Polynom<T>) -> (Polynom<T>, Polynom<T>) {
// 	let mut a = Polynom::from(vec![0; d + 1]);
// 	let mut pp = Polynom::from(vec![0; d + 1]);

// 	for k in (1..(d + 2)).rev() {
// 	    let mut f = Polynom::from(vec![1]);
// 	    let mut fact = T::from(1);
// 	    for i in 1..k {
// 		f = &f * &Polynom::from(vec![i as i64, 1]);
// 		fact = fact * T::from(i as i64);
// 	    }
// 	    a.value[k - 1] = (p.value[k - 1] + pp.value[k - 1]*T::from(-1)) * fact / f.value[k - 1];
// 	    f = Polynom::from(f.value.into_iter().map(|e| e * a.value[k - 1] / fact).collect::<Vec<T>>());
// 	    pp = &pp + &f;
// 	}

// 	let mut pres = Polynom::from(vec![0; d + 1]);
// 	let mut q = Polynom::from(vec![1]);
// 	for k in (0..(d + 1)).rev() {
// 	    let qtmp = Polynom::from(q.value.iter().map(|e| *e * a.value[k]).collect::<Vec<T>>());
// 	    pres = &pres + &qtmp;
// 	    q = &q * &Polynom::from(vec![T::from(1), T::from(-1)*r]);
// 	}

// 	return (pres, q);
//     }

//     fn raise(&self, n: usize) -> Polynom<T> {
// 	let mut res = Polynom::from(vec![1]);
// 	for _ in 0..n {
// 	    res = &res * &self;
// 	}
// 	return res;
//     }

//     fn seq(&self, m: usize) -> Polynom<T> {
// 	let a: &[T] = &self.value;
// 	let mut res = vec![T::from(0); m];
// 	res[0] = T::from(1);
// 	for i in 1..m {
// 	    for j in 1..=i {
// 		res[i] = res[i] + a[j] * res[i - j];
// 	    }
// 	}
// 	return Polynom { value: res };
//     }

//     fn mset(&self, m: usize) -> Polynom<T>
//     {
// 	let mut a: Vec<Vec<T>> = vec![vec![T::from(0); m]; m];
// 	for i in 0..m {
// 	    a[0][i] = T::from(1);
// 	}
// 	for i in 1..m {
// 	    for j in 1..m {
// 		if j < self.value.len() && self.value[j] != T::from(0) {
// 		    for k in 0..=(i / j) {
// 			// println!("i = {}\nj = {}\ni/j = {}\nk = {}", i, j, i / j, k) ;
// 			a[i][j] = a[i][j] + comb::<T>(self.value[j].into() + k - 1, k) * a[i - k * j][j - 1];
// 		    }
// 		} else {
// 		    a[i][j] = a[i][j - 1];
// 		}
// 	    }
// 	}
// 	return Polynom { value: (0..m).map(|i| a[i][i]).collect() };
//     }


}

// fn pair<T>(a: &Polynom<T>, b: &Polynom<T>, m: usize) -> Polynom<T>
// where
//     T: Copy + From<i64> + ops::Add<T, Output = T> + ops::Mul<T, Output = T> + ops::Div<T, Output = T> + Eq
// {
//     let res = a * b;
//     return Polynom { value: res.value.into_iter().take(m).collect() };
// }

// fn car(bytes: &[u8]) -> (u8, &[u8]) {
//     (bytes[0], &bytes[1..])
// }


fn main() {
    
    // let mut scan = Scanner::default();
    // let out = &mut BufWriter::new(stdout());
    
    // let k: usize = scan.next();
    // let n: usize = scan.next();

    // writeln!(out, "{}", Polynom::<Finite>::from(
    // 	(0..=(k - 2)/2)
    // 	    .map(|i| Finite::from(if i % 2 == 0 { 1 } else { -1 } as i64) * comb::<Finite>(k - i - 2, i))
    // 	    .collect::<Vec<Finite>>())
    // 	     .div(&Polynom::<Finite>::from((0..=(k - 1)/2)
    // 					   .map(|i| Finite::from(if i % 2 == 0 { 1 } else { -1 } as i64) * comb::<Finite>(k - i - 1, i))
    // 					   .collect::<Vec<Finite>>()), n)).ok();
}
