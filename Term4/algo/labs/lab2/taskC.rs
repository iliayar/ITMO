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
    rev: usize,
    id: usize
}

struct State<'a> {
    g: &'a Vec<Vec<usize>>,
    edges: &'a mut Vec<Edge>,
    t: usize,
    s: usize
}

fn dfs(v: usize, p: i64, was: &mut [bool], state: &mut State) -> i64 {
    if v == state.t {
	return p;
    }
    was[v] = true;
    for i in state.g[v].iter().cloned() {
	let e: Edge = state.edges[i];
	if !was[e.to] && e.f < e.c {
	    let delta = dfs(e.to, min(p, e.c - e.f), was, state);
	    if delta > 0 {
		state.edges[i].f += delta;
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

fn walk(u: usize, was: &mut [bool], path: &mut Vec<usize>, state: &State) -> bool {
    path.push(u);
    if u == state.t {
	return true;
    }
    for i in state.g[u].iter().cloned() {
	if !was[i] && state.edges[i].f == 1 && i % 2 == 0 {
	    was[i] = true;
	    if walk(state.edges[i].to, was, path, state) {
		return true;
	    }
	}
    }
    return false;
}

fn sol(scan: &mut Scanner, out: &mut dyn Write ) {

    let n = scan.next::<usize>();
    let m = scan.next::<usize>();
    let s = scan.next::<usize>() - 1;
    let t = scan.next::<usize>() - 1;
    let mut g: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut es: Vec<Edge> = Vec::new();
    for i in 0..m {
	let a = scan.next::<usize>() - 1;
	let b = scan.next::<usize>() - 1;
	g[a].push(es.len());
	es.push(Edge { c: 1, from: a, to: b, f: 0, rev: es.len() + 1, id: i });
	g[b].push(es.len());
	es.push(Edge { c: 0, from: b, to: a, f: 0, rev: es.len() - 1, id: i });
    }
    let mut state = State { g: &g, edges: &mut es, t, s };
    let res = ford(&mut state);
    if res >= 2 {
	writeln!(out, "YES").ok();
    } else {
	writeln!(out, "NO").ok();
	return
    }
    let mut mp: Vec<usize> = Vec::new();
    let mut pp: Vec<usize> = Vec::new();
    let mut was = vec![false; 2*m];
    walk(state.s, &mut was, &mut mp, &state);
    walk(state.s, &mut was, &mut pp, &state);
    for u in mp.iter() {
	write!(out, "{} ", u + 1).ok();
    }
    writeln!(out, "").ok();
    for u in pp.iter() {
	write!(out, "{} ", u + 1).ok();
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
