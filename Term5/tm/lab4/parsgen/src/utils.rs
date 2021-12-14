
use termion::*;

pub fn perror<S: AsRef<str>>(msg: S) {
    eprintln!("{}{}error{}: {}{}{}", color::Fg(color::Red), style::Bold, style::Reset, style::Bold, msg.as_ref(), style::Reset);
}

pub fn pwarning<S: AsRef<str>>(msg: S) {
    eprintln!("{}{}warning{}: {}{}{}", color::Fg(color::Yellow), style::Bold, style::Reset, style::Bold, msg.as_ref(), style::Reset);
}
