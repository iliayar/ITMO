#![allow(dead_code)]
#[allow(unused_imports)]
use std::cmp::{min,max};
use std::io::{BufWriter, stdin, stdout, Write, BufRead, BufReader};
use std::iter;
use std::ops;
use std::time::{SystemTime, UNIX_EPOCH};
use std::f64::consts::{PI};

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

#[derive(Clone, Copy, Debug)]
struct Comp {
    re: f64,
    im: f64,
}

impl Comp {
    fn from_exp(x: f64) -> Comp {
	Comp { re: x.cos(), im: x.sin() }
    }

    fn pow(&self, k: usize) -> Comp {
	let mut b: Comp = Comp::from(1f64);
	if k == 0 {
	    return b;
	}
	let mut k = k;
	let mut n = self.clone();
	while k > 1 {
	    if k % 2 == 0 {
		n = n * n;
		k /= 2;
	    } else {
		b = b * n;
		k -= 1;
	    }
	}
	return b * n;
    }
}

impl From<f64> for Comp {
    fn from(x: f64) -> Self {
	Comp { re: x as f64, im: 0 as f64 }
    }
}

impl std::ops::Add<&Comp> for &Comp {
    type Output = Comp;

    fn add(self, rhs: &Comp) -> Self::Output {
	Comp { re: self.re + rhs.re, im: self.im + rhs.im }
    }
}

impl std::ops::Mul<&Comp> for &Comp {
    type Output = Comp;

    fn mul(self, rhs: &Comp) -> Self::Output {
	Comp { re: self.re*rhs.re - self.im*rhs.im, im: self.re*rhs.im + self.im*rhs.re }
    }
}

impl std::ops::Add<Comp> for Comp {
    type Output = Comp;

    fn add(self, rhs: Comp) -> Self::Output {
	&self + &rhs
    }
}

impl std::ops::Mul<Comp> for Comp {
    type Output = Comp;

    fn mul(self, rhs: Comp) -> Self::Output {
	&self * &rhs
    }
}

fn fft(p: &[Comp], inv: bool) -> Vec<Comp>{
    let n = p.len();
    let w = Comp::from_exp(if inv { -1f64 } else { 1f64 } * 2f64*PI/(n as f64));
    if n == 1 {
	return vec![p[0]];
    }
    let p0: Vec<Comp> = p.iter().cloned().step_by(2).collect();
    let p1: Vec<Comp> = p.iter().cloned().skip(1).step_by(2).collect();
    let f = fft(&p0, inv);
    let g = fft(&p1, inv);
    // println!("DBG: n = {:?}, f = {:?}, g = {:?}", n, f , g);
    let mut a: Vec<Comp> = Vec::new();
    for i in 0..n {
	a.push(f[i % (n / 2)] + w.pow(i) * g[i % (n/2)]);
	// println!("DBG: i = {}, a = {:?}", i, a);
    }
    return a;
}

fn furie(p: &[i64], q: &[i64]) -> Vec<i64> {
    let p: Vec<Comp> = p.iter().cloned().map(|e| Comp::from(e as f64)).collect();
    let q: Vec<Comp> = q.iter().cloned().map(|e| Comp::from(e as f64)).collect();
    let a = fft(&p, false);
    // println!("DBG: a = {:?}", a);
    let b = fft(&q, false);
    // println!("DBG: b = {:?}", b);
    let c: Vec<Comp> = a.iter().zip(b.iter()).map(|(l, r)| l*r).collect();
    let res = fft(&c, true);
    return res.iter().cloned().map(|c| (c.re/ (p.len() as f64)).round() as i64).collect();
}


fn sol(scan: &mut Scanner, out: &mut dyn Write ) {
    let s = scan.next::<String>();
    let t = s.as_bytes();
    let mut m = t.len();
    let mut k: u32 = 0;
    while m > 0 {
	k += 1;
	m /= 2;
    }
    // let w = Comp::from_exp(2f64*PI/(2i64.pow(k) as f64));
    // println!("w = {:?}", w);
    // for i in 0..2usize.pow(k) {
    // 	println!("w^{:?} = {:?}", i, w.pow(i));
    // }
    let p: Vec<i64> = t.iter().map(|e| (*e - b'0') as i64).chain(iter::repeat(0)).take((2 as usize).pow(k + 1)).collect();
    // let p: Vec<i64> = (0..n).map(|_| scan.next::<i64>()).collect();
    // let q: Vec<i64> = (0..n).map(|_| scan.next::<i64>()).collect();
    // p.reverse(); q.reverse();
    let res = furie(&p, &p);
    let mut sum: i64 = 0;
    for (r, c) in res.iter().step_by(2).zip(t.iter()) {
	if *c == b'1' {
	    sum += r / 2;
	}
    }
    writeln!(out, "{}", sum).ok(); // 🤔
    // for r in res.iter().take(2*(n - 1) + 1) {
    // 	write!(out, "{} ", r).ok();
    // }
    // writeln!(out, "").ok();
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
