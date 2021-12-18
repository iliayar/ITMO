use clap::{Arg, App};
use std::{process::Command, fs::OpenOptions};
use termion::*;
use std::io::Write;

mod codegen;
mod gen;
mod utils;
mod lalr;
mod parslib;

fn main() {
    let matches = App::new("parsgen")
        .arg(Arg::with_name("lex_file")
             .help("File to generate lexer from")
	     .required(true))
        .arg(Arg::with_name("gramma_file")
             .help("File to generate parser from")
	     .required(true))
        .arg(Arg::with_name("crate")
             .help("Crate directory to put generated file in")
	     .required(true))
        .arg(Arg::with_name("create-crate")
             .help("Create crate if it doesn't exists")
	     .short("c")
	     .long("create-crate"))
        .arg(Arg::with_name("lib")
             .help("If create-crate provided, then makes it lib otherwise binary")
	     .short("l")
	     .long("lib"))
        .arg(Arg::with_name("mod")
             .help("Module name to put parser in")
             .short("-m")
             .long("--mod")
	     .takes_value(true))
        .get_matches();

    let gramma_file = matches.value_of("gramma_file").unwrap();
    let lex_file = matches.value_of("lex_file").unwrap();
    let res_crate = matches.value_of("crate").unwrap();
    let res_mod = matches.value_of("mod").unwrap_or("parser");
    let out_file = format!("{}/src/{}.rs", res_crate, res_mod);
    let create_crate = matches.is_present("create-crate");
    if create_crate {
	let use_lib = matches.is_present("lib");
	Command::new("cargo")
	    .args(["new",  if use_lib { "--lib" } else { "--bin" }, res_crate])
	    .status()
	    .expect("Failed to create crate");

	let mut toml = OpenOptions::new()
	    .write(true)
	    .append(true)
	    .open(format!("{}/Cargo.toml", res_crate))
	    .unwrap();

	writeln!(toml, "termion = \"*\"").ok();
	writeln!(toml, "fancy-regex = \"*\"").ok();
    }
    parslib::put_parslib(res_crate);
    codegen::Generator::new(lex_file, gramma_file, &out_file, res_mod).gen();
    Command::new("rustfmt")
	.args([&out_file])
	.status()
	.expect("Failed to format result file");
    println!("
You need to add imports in the beggining of lib.rs/main.rs:
{}
mod parslib;
mod {};
{}
", color::Fg(color::Green), res_mod, style::Reset);

}
