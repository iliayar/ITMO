#![allow(dead_code)]
use std::cmp::Reverse;
#[allow(unused_imports)]
use std::cmp::{max, min};
use std::collections::BTreeSet;
use std::collections::BinaryHeap;
use std::io::{stdin, stdout, BufRead, BufReader, BufWriter, Write};
use std::iter;
use std::ops;

const FILENAME: &str = "filename";
const IS_FILES: bool = false;

struct Scanner {
    buffer: Vec<String>,
    reader: Box<dyn BufRead>,
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
            reader,
        }
    }
}

//================================ CODE BEGIN ===============================================

const INF: i64 = 1e+18 as i64;

#[derive(Clone, Copy, Debug)]
struct Edge {
    c: i64,
    from: usize,
    to: usize,
    f: i64,
    rev: usize,
    w: i64,
    idx: usize,
}

#[derive(Debug)]
struct State {
    g: Vec<Vec<usize>>,
    edges: Vec<Edge>,
    t: usize,
    s: usize,
}

fn add_edge(c: i64, u: usize, v: usize, w: i64, idx: usize, state: &mut State) {
    add_edge_impl(c, c, u, v, w, idx, state);
}

fn add_or_edge(c: i64, u: usize, v: usize, w: i64, idx: usize, state: &mut State) {
    add_edge_impl(c, 0, u, v, w, idx, state);
}

fn add_edge_impl(c1: i64, c2: i64, u: usize, v: usize, w: i64, idx: usize, state: &mut State) {
    state.g[u].push(state.edges.len());
    state.edges.push(Edge {
        c: c1,
        from: u,
        to: v,
        f: 0,
        rev: state.edges.len() + 1,
        w,
        idx,
    });
    state.g[v].push(state.edges.len());
    state.edges.push(Edge {
        c: c2,
        from: v,
        to: u,
        f: 0,
        rev: state.edges.len() - 1,
        w: -w,
        idx,
    });
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
    let mut res: i64 = 0;
    for i in state.g[state.s].iter().cloned() {
        res += state.edges[i].f.abs();
    }
    return res;
}

fn dijkstra(state: &State) -> (Vec<usize>, i64) {
    let mut d: Vec<i64> = vec![INF; state.g.len()];
    let mut set = BTreeSet::new();
    let mut p: Vec<usize> = vec![0; state.g.len()];
    d[state.s] = 0;
    set.insert((0, state.s));
    while let Some((dv, v)) = set.iter().cloned().next() {
        set.remove(&(dv, v));
        for j in state.g[v].iter().cloned() {
            let e = state.edges[j];
            if d[v] + e.w < d[e.to] && e.f < e.c {
                set.remove(&(d[e.to], e.to));
                d[e.to] = d[v] + e.w;
                p[e.to] = j;
                set.insert((d[e.to], e.to));
            }
        }
    }
    let mut res: Vec<usize> = Vec::new();
    if d[state.t] == INF {
        return (res, INF);
    }

    let mut i = p[state.t];
    loop {
        res.push(i);
        if state.edges[i].from == state.s {
            break;
        }
        i = p[state.edges[i].from];
    }
    // res.reverse();
    return (res, d[state.t]);
}

fn with_delta((path, m): (Vec<usize>, i64), state: &State) -> (Vec<usize>, i64, bool) {
    let mut delta: i64 = INF;
    for e in path.iter().cloned() {
        delta = min(delta, state.edges[e].c - state.edges[e].f);
    }
    return (path, delta, m != INF);
}

fn min_cost(state: &mut State) -> i64 {
    while let (path, delta, true) = with_delta(dijkstra(state), state) {
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

fn sol(scan: &mut Scanner, out: &mut dyn Write) {
    let (n, k): (usize, i64) = (scan.next(), scan.next());
    let s = 2 * n;
    let t = 2 * n + 1;
    let mut state = State {
        g: vec![Vec::new(); 2 * n + 2],
        edges: Vec::new(),
        t,
        s,
    };

    for i in 0..n {
        for j in n..2 * n {
            let w = scan.next::<i64>();
            add_or_edge(1, i, j, w, i * n + j - n, &mut state);
        }
    }

    for i in 0..n {
        add_or_edge(k, s, i, 0, n * n + i, &mut state);
    }
    for i in 0..n {
        add_or_edge(k, n + i, t, 0, n * n + n + i, &mut state);
    }

    let c = min_cost(&mut state);
    writeln!(out, "{}", c).ok();

    let mut state2 = State {
        g: vec![Vec::new(); 2 * n + 2],
        edges: Vec::new(),
        t,
        s,
    };

    let mut ecnt = 0usize;
    for i in 0..n {
        for e in state.g[i].iter() {
            if state.edges[*e].c == 0 || state.edges[*e].f != 1 {
                continue;
            }
            add_or_edge(1, i, state.edges[*e].to, 0, ecnt, &mut state2);
            ecnt += 1;
        }
        add_or_edge(1, s, i, 0, ecnt, &mut state2);
        ecnt += 1;
        add_or_edge(1, n + i, t, 0, ecnt, &mut state2);
        ecnt += 1;
    }

    for _ in 0..k {
        let _ = ford(&mut state2);
        for i in 0..n {
            for e in state2.g[i].iter() {
                if state2.edges[*e].c == 0 || state2.edges[*e].f != 1 {
                    continue;
                }
                write!(out, "{} ", state2.edges[*e].to - n + 1).ok();
                state2.edges[*e].c = 0;
            }
        }
        for edge in state2.edges.iter_mut() {
            edge.f = 0;
        }
        writeln!(out, "").ok();
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
        let mut scan = Scanner::new(Box::new(BufReader::new(
            std::fs::File::open("local.in").expect("Cannot open local.in"),
        )));
        let mut out =
            &mut BufWriter::new(std::fs::File::create("local.out").expect("Cannot open local.out"));
        let now = std::time::Instant::now();
        sol(&mut scan, &mut out);
        writeln!(out, "{}ms", now.elapsed().as_millis()).ok();
    } else {
        if IS_FILES {
            let mut scan = Scanner::new(Box::new(BufReader::new(
                std::fs::File::open(FILENAME.to_owned() + ".in").expect("Cannot open remote input"),
            )));
            let mut out = &mut BufWriter::new(
                std::fs::File::create(FILENAME.to_owned() + ".out")
                    .expect("Cannot open remote output"),
            );
            sol(&mut scan, &mut out);
        } else {
            let mut scan = Scanner::new(Box::new(BufReader::new(stdin())));
            let mut out = &mut BufWriter::new(stdout());
            sol(&mut scan, &mut out);
        }
    }
}
