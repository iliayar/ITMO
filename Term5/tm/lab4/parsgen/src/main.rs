use std::env;
use std::fs::File;
use gramma::parse;
use lib::*;

fn main() {
    let mut args = env::args();
    args.next();
    let filename = args.next().expect("Provide filename");
    let _gramma: Gramma = parse(&File::open(filename).expect("File doesn't exists"));
}
