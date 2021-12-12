use super::lexer::LexerError;
use termion::*;

const NEAR_LINES: usize = 1;

pub fn get_near_lines(input: &str, pos: usize) -> (usize, Vec<&str>, usize, usize) {
    let lines: Vec<&str> = input.lines().collect();
    let mut i = 0usize;
    let mut linen = 0usize;
    for (line, n) in lines.iter().zip(0..) {
	if i + line.len() + 1 >= pos {
	    linen = n;
	    break;
	} else {
	    i += line.len() + 1;
	}
    }
    let pos_in_line = pos - i;

    let begin = linen - NEAR_LINES.min(linen);
    let end = (linen + NEAR_LINES + 1).min(lines.len());
    return (
	begin,
	lines[begin..end].to_vec(),
	linen - begin,
	pos_in_line,
    );
}


pub fn prety_print_error_range(filename: &str, input: &str, begin: usize, end: Option<usize>, msg: &str) {
    let repeat_str = |c: char, n: usize| std::iter::repeat(c).take(n).collect::<String>();

    let (begin_line, lines, linen, linepos) = get_near_lines(input, begin);
    let mut max_num_len = format!("{}", begin_line + lines.len() + 1).len();
    if let Some(end) = end {
	let (begin_line, lines, _, _) = get_near_lines(input, end);
	max_num_len = format!("{}", begin_line + lines.len() + 1).len();
    }
    let prefix_str = |s: &str| format!("{}{}{:>w$} | {}", style::Bold, color::Fg(color::LightBlue), s, style::Reset, w = max_num_len);
    let prefix = |n: usize, begin: usize| prefix_str(&format!("{}", begin + n + 1));
    let underline_line = |i, lines: &[&str], begin_line: usize, begin: usize, end: usize, msg: &str| {
	eprintln!("{}{}", prefix(i, begin_line), lines[i]);
	eprintln!("{}{}{}{}{} {}{}",
		  prefix_str(""), color::Fg(color::Red), style::Bold,
		  repeat_str(' ', begin - 1),
		  repeat_str('^', end - begin + 1),
		  msg, style::Reset);
    };

    let mut i = 0usize;
    eprintln!("{}{}{} -->{} {}:{}:{}",
	      repeat_str(' ', max_num_len - 1), color::Fg(color::LightBlue), style::Bold,
	      style::Reset, filename, begin_line + linen + 1, linepos
    );
    while i < linen && i < lines.len() {
	eprintln!("{}{}", prefix(i, begin_line), lines[i]);
	i += 1;
    }
    if let Some(end) = end {
	let mut cur_linepos = linepos;
	let (end_begin_line, end_lines, end_linen, end_linepos) = get_near_lines(input, end);
	while i < lines.len() && i + begin_line < end_begin_line {
	    underline_line(i, &lines, begin_line, cur_linepos, lines[i].len(), "");
	    i += 1;
	    cur_linepos = 1;
	}
	if i + begin_line < end_begin_line {
	    eprintln!("{}{}{} ...{}",
		      repeat_str(' ', max_num_len - 1), color::Fg(color::LightBlue), style::Bold,
		      style::Reset);
	}
	i = (begin_line + i).max(end_begin_line) - end_begin_line;
	while i < end_linen && i < end_lines.len() {
	    underline_line(i, &end_lines, end_begin_line, cur_linepos, end_lines[i].len(), "");
	    i += 1;
	    cur_linepos = 1;
	}
	underline_line(i, &end_lines, end_begin_line, cur_linepos, end_linepos, msg);
	i += 1;
	while i < end_lines.len() {
	    eprintln!("{}{}", prefix(i, end_begin_line), end_lines[i]);
	    i += 1;
	}
    } else {
	underline_line(i, &lines, begin_line, linepos, linepos, msg);
	i += 1;
	while i < lines.len() {
	    eprintln!("{}{}", prefix(i, begin_line), lines[i]);
	    i += 1;
	}
    }
}

pub fn prety_print_error_at(filename: &str, input: &str, pos: usize, msg: &str) {
    prety_print_error_range(filename, input, pos, None, msg);
}

pub fn prety_print_err_line(msg: &str) {
    eprintln!("{}{}error{}{}: {}{}", style::Bold, color::Fg(color::Red), style::Reset, style::Bold, msg, style::Reset);
}

pub fn prety_print_lex_error(filename: &str, input: &str, err: LexerError) {
    match err {
	LexerError::InvalidToken(pos) => prety_print_invalid_token(filename, input, pos),
    };
}

pub fn prety_print_invalid_token(filename: &str, input: &str, pos: usize) {
    prety_print_err_line("Invalid token met. Could not match any regex");
    prety_print_error_at(filename, input, pos, "could not match token");
}
