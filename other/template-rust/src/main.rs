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

const INF: i64 = 100_000;

#[derive(Clone, Copy)]
struct Edge {
    c: i64,
    from: usize,
    to: usize,
    f: i64,
    rev: usize
}

struct State {
    g: Vec<Vec<usize>>,
    edges: Vec<Edge>,
    t: usize,
    s: usize
}

fn dfs(v: usize, p: i64, was: &mut [bool], state: &mut State) -> i64 {
    if v == state.t {
	return p;
    }
    was[v] = true;
    for i in 0..state.g[v].len() {
	let e: Edge = state.edges[state.g[v][i]];
	if !was[e.to] && e.f < e.c {
	    let delta = dfs(e.to, min(p, e.c - e.f), was, state);
	    if delta > 0 {
		state.edges[state.g[v][i]].f += delta;
		state.edges[e.rev].f -= delta;
		return delta;
	    }
	}
    }
    return 0;
}

fn ford(state: &mut State) -> i64 {
    let mut was: Vec<bool> = vec![false; state.g.len()];
    while dfs(state.s, INF, &mut was, state) > 0 {
	for i in 0..state.g.len() {
	    was[i] = false;
	}
    }
    let mut res: i64  = 0;
    for i in state.g[state.s].iter().cloned() {
	res += state.edges[i].f.abs();
    }
    return res;
}

fn reachable(u: usize, was: &mut [bool], state: &State) {
    was[u] = true;
    for i in state.g[u].iter().cloned() {
	if !was[state.edges[i].to] && state.edges[i].f < state.edges[i].c {
	    reachable(state.edges[i].to, was, state);
	}
    }
}

fn add_edge(c: i64, u: usize, v: usize, state: &mut State) {
    add_edge_impl(c, c, u, v, state);
}

fn add_or_edge(c: i64, u: usize, v: usize, state: &mut State) {
    add_edge_impl(c, 0, u, v, state);
}

fn add_edge_impl(c1: i64, c2:i64, u: usize, v: usize, state: &mut State) {
    state.g[u].push(state.edges.len());
    state.edges.push(Edge { c: c1, from: u, to: v, f: 0, rev: state.edges.len() + 1});
    state.g[v].push(state.edges.len());
    state.edges.push(Edge { c: c2, from: v, to: u, f: 0, rev: state.edges.len() - 1});
}

fn dfs1(u: usize, day: usize, n: usize, path: &mut Vec<(usize, usize)>, state: &mut State) {
    if u == state.t {
	return;
    }
    for i in state.g[u].iter().cloned() {
	let e: Edge = state.edges[i];
	// println!("{} -> {} f = {}", e.from, e.to, e.f);
	if e.f >= 1 {
	    state.edges[i].f -= 1;
	    path.push((e.from - day*n, e.to - (day + 1)*n));
	    dfs1(e.to, day + 1, n, path, state);
	    return;
	}
    }
}

fn sol(scan: &mut Scanner, out: &mut dyn Write ) {
    let (n, m, k, s, t) = (scan.next::<usize>(), scan.next::<usize>(), scan.next::<usize>(), scan.next::<usize>() - 1, scan.next::<usize>() - 1);
    let mut state = State {
        g: Vec::new(),
        edges: Vec::new(),
        t,
        s,
    };
    let mut g: Vec<Vec<usize>> = vec![Vec::new(); n];
    for _ in 0..m {
	let (u, v) = (scan.next::<usize>() - 1, scan.next::<usize>() - 1);
	g[u].push(v);
	g[v].push(u);
    }
    let mut day: usize = 0;
    loop {
	state.g.resize((day + 1)*n + n, Vec::new());
	for i in 0..n {
	    add_or_edge(INF, i + day*n, i + (day + 1)*n, &mut state);
	    for j in g[i].iter().cloned() {
		add_or_edge(1, i + day*n, j + (day + 1)*n, &mut state);
	    }
	}
	state.t += n;
	if ford(&mut state) >= (k as i64) {
	    break;
	}
	day += 1;
    }
    day += 1;
    writeln!(out, "{}", day).ok();
    let mut res: Vec<Vec<(usize, usize)>> = Vec::new();
    for _ in 0..k {
	let mut path: Vec<(usize, usize)> = Vec::new();
	dfs1(state.s, 0, n, &mut path, &mut state);
	res.push(path);
    }
    for i in 0..k {
	while res[i].len() < day {
	    res[i].push((state.t - day*n, state.t - day*n));
	}
    }
    // for i in 0..k {
    // 	println!("{:?}", res[i]);
    // }
    for i in 0..day {
	let mut tmp: Vec<(usize, usize)> = Vec::new();
	for j in 0..k {
	    if res[j][i].0 != res[j][i].1 {
		tmp.push((j, res[j][i].1));
	    }
	}
	write!(out, "{} ", tmp.len()).ok();
	for (u, v) in tmp.iter() {
	    write!(out, " {} {} ", u + 1, v + 1).ok();
	}
	writeln!(out, "").ok();
    }
}

//================================ CODE END =================================================

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

fn sol(scan: &mut Scanner, out: &mut dyn Write ) {


    let k = scan.next::<usize>();
    let mut n = scan.next::<usize>() - 1;

    let a: Vec<Num<Finite>> = (0..k).map(|_| Num::from(scan.next::<i64>())).collect();
    let c: Vec<Num<Finite>> = (0..k).map(|_| Num::from(scan.next::<i64>())).collect();

    let (p, q) = Polynom::from_recursive(&a[..], &c[..]);
    let mut p = p.value.value;
    let mut q = q.value.value;
    p.resize(k + 1, Num::zero());
    q.resize(k + 1, Num::zero());
    // println!("DBG: p = {:?}", p);
    // println!("DBG: q = {:?}", q);

    let mut nq: Vec<Num<Finite>> = vec![Num::zero(); k + 1];
    let mut pt: Vec<Num<Finite>> = vec![Num::zero(); 2*k + 2];
    let mut qt: Vec<Num<Finite>> = vec![Num::zero(); 2*k + 1];
    while n >= k {
	// println!("===========================================");
	for i in 0..=k {
	    if i % 2 == 0 {
		nq[i] = q[i];
	    } else {
		nq[i] = q[i] * Num::from(-1);
	    }
	}
	for i in 0..=(2*k + 1) {
	    pt[i] = Num::zero();
	}
	for i in 0..=2*k {
	    qt[i] = Num::zero();
	}
	for i in 0..=k {
	    for j in 0..=k {
		pt[i + j] = pt[i + j] + p[i] * nq[j];
	    }
	}
	for i in 0..=k {
	    for j in 0..=k {
		qt[i + j] = qt[i + j] + q[i] * nq[j];
	    }
	}

	// println!("DBG: pt = {:?}", pt);
	// println!("DBG: qt = {:?}", qt);

	for i in 0..=k {
	    q[i] = qt[i * 2];
	}
	for i in 0..=k {
	    p[i] = pt[i * 2 + (n % 2)];
	}

	// println!("DBG: p = {:?}", p);
	// println!("DBG: q = {:?}", q);

	n /= 2;
	// println!("DBG: p = {}", p);
	// println!("DBG: q = {}", q);
    }

    let mut a  = vec![Num::from(0); k];
    for i in 0..=n {
	a[i] = p[i];
	for j in 1..=i {
	    a[i] = a[i] - a[i - j] * q[j];
	}
	a[i] = a[i] / q[0];
    }

    writeln!(out, "{}", a[n]).ok();
}

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
