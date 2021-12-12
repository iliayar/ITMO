
use termion::*;

pub fn perror<S: AsRef<str>>(msg: S) {
    eprintln!("{}{}error{}: {}{}{}", color::Fg(color::Red), style::Bold, style::Reset, style::Bold, msg.as_ref(), style::Reset);
}
