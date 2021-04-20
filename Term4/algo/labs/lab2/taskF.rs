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

fn sol(scan: &mut Scanner, out: &mut dyn Write ) {

    let n = scan.next::<usize>();
    let mut state = State { g: vec![Vec::new(); n + 2], edges: Vec::new(), t: n + 1, s: 0 };
    let mut map: Vec<Vec<u8>> = Vec::new();
    let mut has: Vec<i64> = vec![0; n];
    let mut plays: Vec<Vec<bool>> = vec![vec![false; n]; n];
    for i in 0..n {
	map.push(scan.next::<String>().as_bytes().to_vec());
	for j in 0..n {
	    match map[i][j]  {
		b'W' => has[i] += 3,
		b'w' => has[i] += 2,
		b'l' => has[i] += 1,
		b'.' => plays[i][j] = true,
		_ => ()
	    }
	}
    }
    let need: Vec<i64> = (0..n).map(|i| scan.next::<i64>() - has[i]).collect();
    for i in 0..n {
	add_or_edge(plays[i].iter().skip(i).map(|v| if *v { 3 } else { 0 }).sum::<i64>(), state.s, i + 1, &mut state);
	add_or_edge(need[i], i + 1, state.t, &mut state);
	for j in (i + 1)..n {
	    if !plays[i][j] {
		continue;
	    }
	    add_or_edge(3, i + 1, j + 1, &mut state);
	}
    }
    let flow = ford(&mut state);
    for i in 0..n {
	for j in state.g[i + 1].iter().cloned() {
	    let e: Edge = state.edges[j];
	    if e.to == state.t || e.to < e.from {
		continue;
	    }
	    match e.f {
		0 => {
		    map[i][e.to - 1] = b'W';
		    map[e.to - 1][i] = b'L';
		},
		1 => {
		    map[i][e.to - 1] = b'w';
		    map[e.to - 1][i] = b'l';
		},
		2 => {
		    map[i][e.to - 1] = b'l';
		    map[e.to - 1][i] = b'w';
		},
		3 => {
		    map[i][e.to - 1] = b'L';
		    map[e.to - 1][i] = b'W';
		},
		_ => ()
	    }
	}
    }
    map.iter().for_each(|s| writeln!(out, "{}", std::str::from_utf8(s).unwrap()).expect(""));
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
