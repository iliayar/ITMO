use std::fs::File;
use std::io::{BufRead, BufReader};


#[derive(Debug)]
pub struct Error {
    msg: String
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.msg)
    }
}

impl From<std::io::Error> for Error {
    fn from(err: std::io::Error) -> Self {
        Error {
	    msg: format!("IO error: {}", err),
	}
    }
}

impl std::error::Error for Error {
}

pub struct Reader {
    file: BufReader<File>
}

impl Reader {
    pub fn new(filename: String) -> Result<Self, Error> {
	let file = BufReader::new(File::open(filename)?);

	Ok(Self {
	    file
	})
    }

    pub fn read(&mut self) -> Result<Option<String>, Error> {
	let mut line = String::new();
	let read = self.file.read_line(&mut line)?;

	if read == 0 {
	    Ok(None)
	} else {
	    line.pop();
	    Ok(Some(line))
	}
    }
}
