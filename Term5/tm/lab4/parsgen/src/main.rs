use clap::{Arg, App};
use std::process::Command;

mod gen;

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
    if matches.is_present("create-crate") {
	Command::new("cargo")
	    .args(["new", /* "--lib",*/ res_crate])
	    .status()
	    .expect("Failed to create crate");
    }
    gen::Generator::new(lex_file, gramma_file, &out_file, res_mod).gen();
    Command::new("rustfmt")
	.args([&out_file])
	.status()
	.expect("Failed to format result file");
}
