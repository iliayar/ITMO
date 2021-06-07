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


fn karacuba(p: &[i64], q: &[i64]) -> Vec<i64> {
    let n = p.len();
    assert_eq!(n, q.len());
    // println!("DBG: {}", n);
    // if n == 0 {
    // 	return vec![];
    // }
    if n == 1 {
	return vec![p[0] * q[0]];
    }    
    let (p1, p2) = p.split_at(n/2);
    let (q1, q2) = q.split_at(n/2);
    // let p_sum: Vec<i64> = p1.iter().zip(p2).map(|(a, b)| *a + *b).collect();
    // let q_sum: Vec<i64> = q1.iter().zip(q2).map(|(a, b)| *a + *b).collect();
    let mut p_sum: Vec<i64> = vec![0; max(p1.len(), p2.len())];
    let mut q_sum: Vec<i64> = vec![0; max(q1.len(), q2.len())];
    for i in 0..max(p1.len(), p2.len()) {
	if i < p1.len() {
	    p_sum[i] += p1[i];
	}
	if i < p2.len() {
	    p_sum[i] += p2[i];
	}
    }
    for i in 0..max(q1.len(), q2.len()) {
	if i < q1.len() {
	    q_sum[i] += q1[i];
	}
	if i < q2.len() {
	    q_sum[i] += q2[i];
	}
    }

    // println!("DBG: P: {:?} + {:?} = {:?}", p1, p2, p_sum);
    // println!("DBG: Q: {:?} + {:?} = {:?}", q1, q2, q_sum);

    let rm = karacuba(&p_sum, &q_sum);
    let rl = karacuba(&p1, &q1);
    let rr = karacuba(&p2, &q2);

    // println!("rm = {:?}", rm);
    // println!("rl = {:?}", rl);
    // println!("rr = {:?}", rr);
    
    let mut res: Vec<i64> = vec![0; 2*n - 1];
    for i in 0..rm.len() {
	res[n/2 + i] += rm[i];
    }
    for i in 0..rl.len() {
	res[i] += rl[i];
	res[n/2 + i] -= rl[i];
    }
    for i in 0..rr.len() {
	res[2*(n/2) + i] += rr[i];
	res[n/2 + i] -= rr[i];
    }

    // println!("RES: {:?} * {:?} = {:?}", p, q, res);
    return res;
}

fn sol(scan: &mut Scanner, out: &mut dyn Write ) {
    let n = scan.next::<usize>() + 1;
    // let mut m = n;
    // let mut k: u32 = 0;
    // while m > 0 {
    // 	k += 1;
    // 	m /= 2;
    // }
    // let p: Vec<i64> = (0..n).map(|_| scan.next::<i64>()).chain(iter::repeat(0)).take((2 as usize).pow(k)).collect();
    // let q: Vec<i64> = (0..n).map(|_| scan.next::<i64>()).chain(iter::repeat(0)).take((2 as usize).pow(k)).collect();
    let p: Vec<i64> = (0..n).map(|_| scan.next::<i64>()).collect();
    let q: Vec<i64> = (0..n).map(|_| scan.next::<i64>()).collect();
    // p.reverse(); q.reverse();
    let res = karacuba(&p, &q);
    for r in res.iter().take(2*(n - 1) + 1) {
	write!(out, "{} ", r).ok();
    }
    writeln!(out, "").ok();
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
