use clap::Parser;
use log::*;

use super::args::Args;
use super::rand::Rand;
use super::reader::Reader;

#[derive(Debug)]
pub struct Error {
    msg: String
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.msg)
    }
}

impl From<super::reader::Error> for Error {
    fn from(err: super::reader::Error) -> Self {
        Error {
	    msg: format!("Reader error: {}", err),
	}
    }
}

impl std::error::Error for Error {
}

pub struct App {
    args: Args,
}

impl App {
    pub fn new() -> Self {
	let args = Args::parse();

	Self {
	    args
	}
    }

    pub fn start(self) -> Result<(), Error> {
	debug!("App started");
	let rand = Rand::new(self.args.parameter, 1, self.args.numbilets);
	let mut reader = Reader::new(self.args.file)?;

	while let Some(name) = reader.read()? {
	    let bilet = rand.get(&name);
	    println!("{}: {}", name, bilet);
	}

	Ok(())
    }
}
