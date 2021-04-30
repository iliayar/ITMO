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

const MOD: u128 =  998_244_353;

/// returns (g, x, y)
fn gcdext(a: i64, b: i64) -> (i64, i64, i64) {
    if a == 0 {
	return (b, 0, 1);
    }
    let (d, x, y) = gcdext(b % a, a);
    (d, y - (b / a) * x, x)
}

#[derive(Clone,Copy)]
struct Finite {
    value: u128
}

fn comb<T>(n: usize, k: usize) -> T
where
    T: From<i64>
    + std::ops::Mul<T, Output = T>
    + std::ops::Div<T, Output = T>
{
    let mut res = T::from(1 as i64);
    for i in (n - k + 1)..=n {
	res = res * T::from(i as i64);
    }
    for i in 1..=k {
	res = res / T::from(i as i64);
    }
    return res;
}
    
impl Finite {
    fn invert(&self) -> Finite {
	let (g, x, _) = gcdext(self.value as i64, MOD as i64);
	if g != 1 {
	    panic!("Should find inverted");
	} else {
	    Finite::from(x)
	}
    }
}

impl From<i64> for Finite {
    fn from(value: i64) -> Self {
	let mut value = value;
	while value < 0 {
	    value += MOD as i64;
	}
        return Finite { value: (value as u128) % MOD };
    }
}

impl Into<usize> for Finite {
    fn into(self) -> usize {
        self.value as usize
    }
}

impl From<u128> for Finite {
    fn from(value: u128) -> Self {
        return Finite { value: value % MOD };
    }
}

impl std::fmt::Display for Finite {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl std::fmt::Debug for Finite {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl ops::Add<&Finite> for &Finite {
    type Output = Finite;

    fn add(self, rhs: &Finite) -> Self::Output {
	// if self.value.checked_add(rhs.value).is_none() {
	//     let n = self.value / 2;
	//     return (rhs +  &Finite::from(n)) + (rhs + &Finite::from(self.value - n)); 
	// }
        return Finite::from((self.value + rhs.value) % MOD);
    }
}

impl ops::Add<Finite> for Finite {
    type Output = Finite;

    fn add(self, rhs: Finite) -> Self::Output {
        return &self + &rhs;
    }
}

impl std::iter::Sum<Finite> for Finite {
    fn sum<I: Iterator<Item = Finite>>(iter: I) -> Self {
        iter.fold(Finite::from(0 as i64), |acc, x| acc + x)
    }
}

impl ops::Mul<Finite> for Finite {
    type Output = Finite;

    fn mul(self, rhs: Finite) -> Self::Output {
	if self.value.checked_mul(rhs.value).is_none() {
	    // let n = self.value / 2;
	    // return rhs * Finite::from(n) + rhs * Finite::from(self.value - n); 
	}
        return Finite::from((self.value * rhs.value) % MOD);
    }
}

impl ops::Div<Finite> for Finite {
    type Output = Finite;

    fn div(self, rhs: Finite) -> Self::Output {
        return self * rhs.invert();
    }
}

impl ops::Sub<Finite> for Finite {
    type Output = Finite;

    fn sub(self, rhs: Finite) -> Self::Output {
        return self + Finite::from(-1 as i64)*rhs;
    }
}

impl PartialEq for Finite {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl Eq for Finite {}

#[derive(Clone,Copy)]
struct Rational {
    denominator: i64,
    numerator: i64
}

impl PartialEq for Rational {
    fn eq(&self, other: &Self) -> bool {
        return self.numerator == other.numerator && self.denominator == other.denominator;
    }
}

impl Eq for Rational {}

impl Rational {
    fn new(numerator: i64, denominator: i64) -> Rational {
	let numer = if denominator < 0 { -numerator } else { numerator };
	let denom = if denominator < 0 { -denominator } else { denominator };
	let d = gcdext(if numer < 0 { -numer } else { numer }, denom).0;
	Rational {
	    denominator: denom / d,
	    numerator: numer / d,
	}
    }
}

impl Into<usize> for Rational {
    fn into(self) -> usize {
        self.numerator as usize
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
	let mlt: i64 = gcdext(self.denominator, rhs.denominator).0;
	let denom: i64 = self.denominator * rhs.denominator / mlt;
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

impl ops::Div<Rational> for Rational {
    type Output = Rational;

    fn div(self, rhs: Rational) -> Self::Output {
        return self * Rational::new(rhs.denominator, rhs.numerator);
    }
}

impl From<i64> for Rational {
    fn from(numer: i64) -> Self {
        Rational::new(numer, 1)
    }
}

struct Polynom<T> {
    value: Vec<T>
}

impl<T> std::fmt::Display for Polynom<T>
where T: std::fmt::Display
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for t in self.value.iter() {
	    write!(f, "{} ", t)?;
	}
	Ok(())
    }
}

impl<T, V> From<Vec<V>> for Polynom<T>
where T: From<V>,
      V: Copy
{
    fn from(p: Vec<V>) -> Self {
        return Polynom { value: p.iter().map(|e| T::from(*e)).collect() };
    }
}

impl<T> ops::Add<&Polynom<T>> for &Polynom<T>
where
    T: Copy + From<i64> + ops::Add<T, Output = T>
{
    type Output = Polynom<T>;

    fn add(self, rhs: &Polynom<T>) -> Self::Output {
	let a: &[T] = &self.value;
	let b: &[T] = &rhs.value;

	let mut p = vec![T::from(0); std::cmp::max(a.len(), b.len())];
	for i in 0..p.len() {
	    p[i] = if i >= a.len() {
		T::from(0)
	    } else {
		a[i]
	    } + if i >= b.len() {
		T::from(0)
	    } else {
		b[i]
	    };
	}
	return Polynom { value: p };
    }
}

impl<T> ops::Mul<&Polynom<T>> for &Polynom<T>
where
    T: Copy + From<i64> + ops::Add<T, Output = T> + ops::Mul<T, Output = T>
{
    type Output = Polynom<T>;

    fn mul(self, rhs: &Polynom<T>) -> Self::Output {
	let a: &[T] = &self.value;
	let b: &[T] = &rhs.value;
	let mut p = vec![T::from(0); a.len() + b.len() - 1];
	for i in 0..a.len() {
	    for j in 0..b.len() {
		p[i + j] = p[i + j] + a[i] * b[j];
	    }
	}
	return Polynom { value: p };
    }
}

impl<T> Polynom<T>
where
    T: Copy
    + From<i64>
    + ops::Add<T, Output = T>
    + ops::Mul<T, Output = T>
    + ops::Div<T, Output = T>
    + Eq
    + std::fmt::Display
    + Into<usize>
{
    fn div(&self, rhs: &Polynom<T>, size: usize) -> Polynom<T> {
	let a: &[T] = &self.value;
	let b: &[T] = &rhs.value;
	// let mut max_zero: usize = 0;
	// while b[max_zero] == T::from(0) {
	//     max_zero += 1;
	// }
	// let b: &[T] = &b[max_zero..];
	let mut p = vec![T::from(0); size];
	for i in 0..p.len() {
	    let mut sum: T = T::from(0);
	    for j in 0..i {
		sum = sum + p[j] * if i - j >= b.len() { T::from(0) } else { b[i - j] };
	    }
	    p[i] = (if i >= a.len() { T::from(0) } else { a[i] } + T::from(-1)*sum) / b[0];
	}
	let res = Polynom { value: p };
	// let res = Polynom { value: p.iter().cloned().skip(max_zero).collect() };
	// println!("Div: {}", res);
	return res;
    }

    fn subs(&self, arg: &Polynom<T>) -> Polynom<T> {
	let a: &[T] = &self.value;
	let b: &[T] = &arg.value;
	let size = (a.len() - 1)*(b.len() - 1) + 1;
	let mut p = vec![T::from(0); size];
	let mut bn = vec![T::from(0); size + b.len()];
	let mut bnt = vec![T::from(0); size + b.len()];
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
		bn[j] = T::from(0);
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

    fn exp(size: usize) -> Polynom<T> {
	let mut p = vec![T::from(0); size];
	let mut fact: T = T::from(1);
	for i in 0..size {
	    let n = T::from(i as i64);
	    p[i] = T::from(1) / fact;
	    fact = fact * (n + T::from(1));
	}
	return Polynom { value: p };
    }

    fn sqrt(size: usize) -> Polynom<T> {
	let mut p = vec![T::from(0); size];
	let mut fact1: T = T::from(1);
	let mut fact2: T = T::from(1);
	let mut pow: T = T::from(1);
	for i in 0..size {
	    let n = T::from(i as i64);
	    let sign = if i % 2 == 0 { 1 } else { -1 };
	    p[i] = fact2;
	    let mut t: T = T::from(1) + T::from(-2)*n;
	    t = T::from(sign) * t * fact1 * fact1 * pow;
	    p[i] = p[i] / t;
	    fact2 = fact2 * (T::from(2)*n + T::from(1)) * (T::from(2)*n + T::from(2));
	    fact1 = fact1 * (n + T::from(1));
	    pow = pow * T::from(4);
	}
	return Polynom { value: p };
    }

    fn ln(size: usize) -> Polynom<T> {
	let mut p = vec![T::from(0); size];
	for i in 1..size {
	    let n = T::from(i as i64);
	    p[i] = T::from(1) / n;
	    let sign = if i % 2 == 0 { -1 } else { 1 };
	    p[i] = p[i] * T::from(sign);
	}
	return Polynom { value: p };
    }

    fn from_recursive(a: &[T], c: &[T]) -> (Polynom<T>, Polynom<T>) {
	let mut p: Vec<T> = a.iter().cloned().collect();
	let mut last_nonz: usize = 0;
	for i in 0..c.len() {
	    for j in 0..min(c.len(), i) {
		p[i] = p[i] + T::from(-1) * a[i - j - 1]*c[j];
	    }
	    if p[i] != T::from(0) {
		last_nonz = i;
	    }
	}
	p.resize(last_nonz + 1, T::from(0));
	let q: Vec<T> = iter::once(T::from(1)).into_iter().chain(c.iter().map(|e| *e*T::from(-1))).collect();
	return (Polynom { value: p }, Polynom { value: q });
    }

    fn to_quazi(self, k: usize, r: T) -> Vec<T> {
	let mut res = Polynom::from(vec![]);
	let mut fact: T = T::from(1);
	for i in 1..(k + 1) {
	    fact = fact * T::from(i as i64);
	}
	let mut pow: T = T::from(1);
	for n in 0..self.value.len() {
	    let mut pp = Polynom::from(vec![1]);
	    for i in 1..(k + 1) {
		pp = &pp * &Polynom::from(vec![(i as i64) - (n as i64), 1]);
	    }
	    pp = Polynom { value: pp.value.iter().map(|e| *e * self.value[n] / pow / fact).collect() };
	    res = &res + &pp;
	    pow = pow * r;
	}
	return res.value;
    }

    fn from_quazi(r: T, d: usize, p: Polynom<T>) -> (Polynom<T>, Polynom<T>) {
	let mut a = Polynom::from(vec![0; d + 1]);
	let mut pp = Polynom::from(vec![0; d + 1]);

	for k in (1..(d + 2)).rev() {
	    let mut f = Polynom::from(vec![1]);
	    let mut fact = T::from(1);
	    for i in 1..k {
		f = &f * &Polynom::from(vec![i as i64, 1]);
		fact = fact * T::from(i as i64);
	    }
	    a.value[k - 1] = (p.value[k - 1] + pp.value[k - 1]*T::from(-1)) * fact / f.value[k - 1];
	    f = Polynom::from(f.value.into_iter().map(|e| e * a.value[k - 1] / fact).collect::<Vec<T>>());
	    pp = &pp + &f;
	}

	let mut pres = Polynom::from(vec![0; d + 1]);
	let mut q = Polynom::from(vec![1]);
	for k in (0..(d + 1)).rev() {
	    let qtmp = Polynom::from(q.value.iter().map(|e| *e * a.value[k]).collect::<Vec<T>>());
	    pres = &pres + &qtmp;
	    q = &q * &Polynom::from(vec![T::from(1), T::from(-1)*r]);
	}

	return (pres, q);
    }

    fn raise(&self, n: usize) -> Polynom<T> {
	let mut res = Polynom::from(vec![1]);
	for _ in 0..n {
	    res = &res * &self;
	}
	return res;
    }

    fn seq(&self, m: usize) -> Polynom<T> {
	let a: &[T] = &self.value;
	let mut res = vec![T::from(0); m];
	res[0] = T::from(1);
	for i in 1..m {
	    for j in 1..=i {
		res[i] = res[i] + a[j] * res[i - j];
	    }
	}
	return Polynom { value: res };
    }

    fn mset(&self, m: usize) -> Polynom<T>
    {
	let mut a: Vec<Vec<T>> = vec![vec![T::from(0); m]; m];
	for i in 0..m {
	    a[0][i] = T::from(1);
	}
	for i in 1..m {
	    for j in 1..m {
		if j < self.value.len() && self.value[j] != T::from(0) {
		    for k in 0..=(i / j) {
			// println!("i = {}\nj = {}\ni/j = {}\nk = {}", i, j, i / j, k) ;
			a[i][j] = a[i][j] + comb::<T>(self.value[j].into() + k - 1, k) * a[i - k * j][j - 1];
		    }
		} else {
		    a[i][j] = a[i][j - 1];
		}
	    }
	}
	return Polynom { value: (0..m).map(|i| a[i][i]).collect() };
    }


}

fn pair<T>(a: &Polynom<T>, b: &Polynom<T>, m: usize) -> Polynom<T>
where
    T: Copy + From<i64> + ops::Add<T, Output = T> + ops::Mul<T, Output = T> + ops::Div<T, Output = T> + Eq
{
    let res = a * b;
    return Polynom { value: res.value.into_iter().take(m).collect() };
}

fn car(bytes: &[u8]) -> (u8, &[u8]) {
    (bytes[0], &bytes[1..])
}


fn main() {
    
    let mut scan = Scanner::default();
    let out = &mut BufWriter::new(stdout());
    
    let k: usize = scan.next();
    let n: usize = scan.next();

    writeln!(out, "{}", Polynom::<Finite>::from(
	(0..=(k - 2)/2)
	    .map(|i| Finite::from(if i % 2 == 0 { 1 } else { -1 } as i64) * comb::<Finite>(k - i - 2, i))
	    .collect::<Vec<Finite>>())
	     .div(&Polynom::<Finite>::from((0..=(k - 1)/2)
					   .map(|i| Finite::from(if i % 2 == 0 { 1 } else { -1 } as i64) * comb::<Finite>(k - i - 1, i))
					   .collect::<Vec<Finite>>()), n)).ok();
}
