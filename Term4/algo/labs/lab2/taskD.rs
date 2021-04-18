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
    im: bool
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

fn add_edge(c: i64, u: usize, v: usize, state: &mut State, im: bool) {
    add_edge_impl(c, c, u, v, state, im);
}

fn add_or_edge(c: i64, u: usize, v: usize, state: &mut State, im: bool) {
    add_edge_impl(c, 0, u, v, state, im);
}

fn add_edge_impl(c1: i64, c2:i64, u: usize, v: usize, state: &mut State, im: bool) {
    state.g[u].push(state.edges.len());
    state.edges.push(Edge { c: c1, from: u, to: v, f: 0, rev: state.edges.len() + 1, im});
    state.g[v].push(state.edges.len());
    state.edges.push(Edge { c: c2, from: v, to: u, f: 0, rev: state.edges.len() - 1, im});
}

fn sol(scan: &mut Scanner, out: &mut dyn Write ) {

    let m = scan.next::<usize>();
    let n = scan.next::<usize>();
    let mut state = State { g: vec![Vec::new(); 2 * n * m], edges: Vec::new(), t: 2 * m * n, s: 2 * m * n };
    let mut map: Vec<Vec<u8>> = Vec::new();
    for i in 0..m {
	map.push(scan.next::<String>().as_bytes().to_vec());
	for j in 0..n {
	    let u = i*n + j;
	    add_or_edge(if map[i][j] == b'.' { 1 } else { INF }, u, m*n + u, &mut state, true);
	    if map[i][j] == b'A' {
		state.s = m*n + u;
	    } else if map[i][j] == b'B' {
		state.t = u;
	    }
	    let mut add_edge = |k: usize, l: usize| {
		let v = k*n + l;
		let mut add_with_c = |c: i64| {
		    add_or_edge(c, m*n + u, v, &mut state, false);
		    add_or_edge(c, m*n + v, u, &mut state, false);
		};
		
		if map[i][j] == b'#' || map[k][l] == b'#' {
		    return;
		} else {
		    add_with_c(INF);
		}
	    };
	    if i != 0 {
		add_edge(i - 1, j);
	    }
	    if j != 0 {
		add_edge(i, j - 1);
	    }
	}
    }
    if state.t == 2*m*n || state.s == 2*m*n {
	writeln!(out, "-1").ok();
	return;
    }
    let res = ford(&mut state);
    if res >= INF {
	writeln!(out, "-1").ok();
	return;
    }
    writeln!(out, "{}", res).ok();

    let mut was = vec![false; 2*n*m];
    reachable(state.s, &mut was, &state);
    for e in state.edges.iter().step_by(2) {
	if was[e.from] != was[e.to] && e.im {
	    let (i, j) = (e.from / n, e.from % n);
	    if map[i][j] == b'.' {
		map[i][j] = b'+';
	    }
	}
    }
    for i in 0..m {
	writeln!(out, "{}", std::str::from_utf8(&map[i]).unwrap()).ok();
    }
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
