mod lib;
use std::io::{BufRead, Write};

pub use lib::*;
use log::*;

fn print_tokens(
    out: &mut impl std::io::Write,
    tokens: &Vec<Box<dyn Token>>,
) -> Result<(), PrintError> {
    for token in tokens.iter() {
        print_token(token.as_ref(), out)?;
        out.write(&[b' '])?;
    }

    Ok(())
}

fn tokens_to_string(tokens: &Vec<Box<dyn Token>>) -> Result<String, anyhow::Error> {
    let mut res = Vec::<u8>::new();
    print_tokens(&mut res, tokens)?;
    Ok(String::from_utf8(res)?)
}

fn perform() -> Result<(), anyhow::Error> {
    print!("Input: ");
    std::io::stdout().flush()?;

    let mut line = String::new();
    std::io::stdin().read_line(&mut line)?;

    println!("---------------------------");

    let tokens = tokenize(&line)?;
    let rpn = parse(tokens)?;
    println!("RPN: {}", tokens_to_string(&rpn)?);

    let evaluated = eval(&rpn)?;
    println!("Evaluated: {}", evaluated);

    Ok(())
}

fn main() -> Result<(), anyhow::Error> {
    env_logger::init();

    loop {
        if let Err(err) = perform() {
            error!("{}", err);
        }

        println!("===========================");
    }
}
