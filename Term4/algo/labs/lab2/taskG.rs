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

#[derive(Clone, Copy, Debug)]
struct Edge {
    c: i64,
    from: usize,
    to: usize,
    f: i64,
    rev: usize,
    w: i64
}

#[derive(Debug)]
struct State {
    g: Vec<Vec<usize>>,
    edges: Vec<Edge>,
    t: usize,
    s: usize
}

fn add_edge(c: i64, u: usize, v: usize, w: i64, state: &mut State) {
    add_edge_impl(c, c, u, v, w, state);
}

fn add_or_edge(c: i64, u: usize, v: usize, w: i64, state: &mut State) {
    add_edge_impl(c, 0, u, v, w, state);
}

fn add_edge_impl(c1: i64, c2:i64, u: usize, v: usize, w: i64, state: &mut State) {
    state.g[u].push(state.edges.len());
    state.edges.push(Edge { c: c1, from: u, to: v, f: 0, rev: state.edges.len() + 1, w});
    state.g[v].push(state.edges.len());
    state.edges.push(Edge { c: c2, from: v, to: u, f: 0, rev: state.edges.len() - 1, w: -w});
}

fn ford(state: &State) -> (Vec<usize>, i64) {
    let mut a: Vec<Vec<i64>> = vec![vec![INF; state.g.len()]; state.g.len()];
    let mut p: Vec<Vec<usize>> = vec![vec![0; state.g.len()]; state.g.len()];
    a[state.s][0] = 0;
    for i in 1..state.g.len() {
	for j in 0..state.edges.len() {
	    let e: Edge = state.edges[j];
	    if a[e.to][i] > a[e.from][i - 1] + e.w && e.f < e.c {
		a[e.to][i] = a[e.from][i - 1] + e.w;
		p[e.to][i] = j;
	    }
	}
    }
    let mut j = 0;
    let mut m = INF;
    for i in 0..state.g.len() {
	if a[state.t][i] < m {
	    j = i;
	    m = a[state.t][i];
	}
    }
    let mut res: Vec<usize> = vec![0; j];
    let mut i = p[state.t][j];
    let n = j;
    while j > 0 {
	res[n - j] = i;
	j -= 1;
	i = p[state.edges[i].from][j];
    }
    return (res, m);
}

fn ford_with_delta(state: &State) -> (Vec<usize>, i64, bool) {
    let (path, m) = ford(state);
    let mut delta: i64 = INF;
    for e in path.iter().cloned() {
	delta = min(delta, state.edges[e].c - state.edges[e].f);
    }
    return (path, delta, m != INF);
}

fn min_cost(state: &mut State) -> i64 {
    while let (path, delta, true) = ford_with_delta(state) {
	for e in path {
	    let edge = state.edges[e];
	    state.edges[e].f += delta;
	    state.edges[edge.rev].f -= delta;
	}
    }
    let mut res: i64 = 0;
    for e in state.edges.iter().step_by(2) {
	res += e.f * e.w;
    }
    return res;
}

fn sol(scan: &mut Scanner, out: &mut dyn Write ) {
    let n = scan.next::<usize>();
    let m = scan.next::<usize>();
    let mut state = State {
        g: vec![Vec::new(); n],
        edges: Vec::new(),
        t: n - 1,
        s: 0,
    };
    for _ in 0..m {
	let (u, v, c, w) = (scan.next::<usize>() - 1, scan.next::<usize>() - 1, scan.next::<i64>(), scan.next::<i64>());
	add_or_edge(c, u, v, w, &mut state);
    }
    writeln!(out, "{}", min_cost(&mut state)).ok();
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
