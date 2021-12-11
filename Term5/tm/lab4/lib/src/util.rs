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

pub fn prety_print_error_at(filename: &str, input: &str, pos: usize, msg: &str) {
    let repeat_str = |c: char, n: usize| std::iter::repeat(c).take(n).collect::<String>();

    let (begin_line, lines, linen, linepos) = get_near_lines(input, pos);
    let max_num_len = format!("{}", begin_line + lines.len() + 1).len();
    eprintln!("{}{}{}-->{} {}:{}:{}",
	      repeat_str(' ', max_num_len - 1), color::Fg(color::LightBlue), style::Bold,
	      style::Reset, filename, begin_line + linen + 1, linepos
    );
    let prefix_str = |s: &str| format!("{}{}{:>w$}| {}", style::Bold, color::Fg(color::LightBlue), s, style::Reset, w = max_num_len);
    let prefix = |n: usize| prefix_str(&format!("{}", begin_line + n + 1));
    let mut i = 0usize;
    while i < linen && i < lines.len() {
	eprintln!("{}{}", prefix(i), lines[i]);
	i += 1;
    }
    eprintln!("{}{}", prefix(i), lines[i]);
    eprintln!("{}{}{}{}{} {}{}",
	      prefix_str(""), color::Fg(color::Red), style::Bold,
	      repeat_str(' ', linepos - 1),
	      repeat_str('^', lines[i].len() - linepos + 1),
	      msg, style::Reset);
    i += 1;
    while i < lines.len() {
	eprintln!("{}{}", prefix(i), lines[i]);
	i += 1;
    }
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
