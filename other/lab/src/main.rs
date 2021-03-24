use std::fs::File;
use std::io::{self, Read};


struct Scanner<'a> {
    pos: usize,
    len: usize,
    eof: bool,
    source: &'a mut dyn Read,
    buffer: [u8; 64]
}

impl<'a> Scanner<'a> {
    fn std(stdin: &'a mut io::Stdin) -> Scanner<'a> {
	Scanner {
	    pos: 0,
	    len: 0,
	    eof: false,
	    source: stdin,
	    buffer: [0; 64]
	}
    }

    fn file(file: &'a mut File) -> Scanner<'a> {
	Scanner {
	    pos: 0,
	    len: 0,
	    eof: false,
	    source: file,
	    buffer: [0; 64]
	}
    }

    fn read_int(&mut self) -> Option<u64> {
	self.skip_whitespaces();
	let mut s = String::new();
	while let Some(c) = self.test_digit() {
	    s.push(c as char);
	}
	return s.parse().ok()
    }

    fn read_vec(&mut self, count: usize) -> Result<Vec<u64>, Vec<u64>> {
	let mut vec = Vec::new();
	for i in 0..count {
	    if let Some(n) = self.read_int() {
		vec.push(n);
	    } else {
		return Err(vec);
	    }
	}
	return Ok(vec);
    }

    fn is_eof(&self) -> bool {
	self.eof
    }

    fn fill(&mut self) -> io::Result<usize> {
	self.source.read(&mut self.buffer)
    }

    fn test(&mut self, c: u8) -> bool {
	if let Some(ch) = self.get_char() {
	    if ch == c {
		self.next_char();
		return true;
	    }
	}
	return false;
    }

    fn check_size(&mut self) {
	if self.pos >= self.len {
	    if let Ok(len) = self.fill() {
		self.len = len;
		self.pos = 0;
	    } else {
		self.eof = true;
	    }
	}
    }
    
    fn get_char(&mut self) -> Option<u8> {
	self.check_size();
	if !self.is_eof() {
	    Some(self.buffer[self.pos])
	} else {
	    None
	}
    }

    fn next_char(&mut self) {
	self.pos += 1;
    }

    fn test_chars(&mut self, range: &Vec<u8>) -> Option<u8> {
	for c in range.iter() {
	    if self.test(*c) {
		return Some(*c)
	    };
	}
	None
    }
    
    fn test_digit(&mut self) -> Option<u8> {
	self.test_chars(&(b'0'..b'9').collect())
    }

    fn skip_whitespaces(&mut self) {
	while let Some(_) = self.test_chars(&vec![b'\n', b' ', b'\t']) {
	}
    }


}

fn sol(scanner: &mut Scanner) {

    let n = scanner.read_int().unwrap();
    let m = scanner.read_int().unwrap();
    let a = scanner.read_vec(n as usize).unwrap();
    println!("{:?}", a);
}

fn main() {
    let local = false;
    let mut stdin;
    let mut file;

    let mut args_iter = std::env::args();
    args_iter.next();
    let local = if let Some(arg1) = args_iter.next() {
	if arg1 == "LOCAL" {
	    true
	} else {
	    false
	}
    } else {
	false
    };

    let mut scanner = if local {
	stdin = io::stdin();
	Scanner::std(&mut stdin)
    } else {
	file = File::open("local.in").expect("Cannot open input file");
	Scanner::file(&mut file)
    };

    sol(&mut scanner);
}
