use super::parser::*;
use super::tokenizer::Token;
use std::{fs::File, io::Write};

fn node_to_string(node: &NodeValue) -> String {
    match node {
	NodeValue::Terminal(t) => {
	    match t {
		Token::IDENTIFIER(t) => t.clone(),
		Token::LPAREN => "(".to_owned(),
		Token::RPAREN => ")".to_owned(),
		Token::COMMA => ",".to_owned(),
		Token::ASTERISK => "*".to_owned(),
		Token::SEMICOLON => ";".to_owned(),
		Token::END => "$".to_owned(),
	    }
	},
	NodeValue::NonTerminal(t) => {
	    t.clone()
	}
    }
}

pub fn draw_tree(tree: &Tree, filename: &str) {
    let mut file = File::create(filename).expect("Cannot open output file");
    writeln!(file, "digraph parse_tree {{").ok();
    writeln!(file, "ratio = fill;").ok();
    writeln!(file, "node [style=filled];").ok();
    let mut n = 0usize;
    draw_node(tree, &mut n, &mut file);
    writeln!(file, "}}").ok();
}

fn draw_node(tree: &Tree, n: &mut usize, file: &mut File) {
    *n += 1;
    let cur_n: usize = *n;
    writeln!(file, "n{} [label=\"{}\"]", cur_n, node_to_string(&tree.value)).ok();
    for node in tree.childs.iter() {
	let last_n = *n;
	draw_node(node, n, file);
	writeln!(file, "n{} -> n{}", cur_n, last_n + 1).ok();
    }
}
