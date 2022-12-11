use rstest::*;

use crate::*;

#[rstest]
#[case("1 + 2 - 3", "1 2 + 3 - ", 0)]
#[case("1 - 2 + 3 - 4 + 5 - 6", "1 2 - 3 + 4 - 5 + 6 - ", -3)]
#[case("1 - (1 + 1) - (2 - 1)", "1 1 1 + - 2 1 - - ", -2)]
#[case("2 + 2 * 2", "2 2 2 * + ", 6)]
#[case("(2 + 2) * 2", "2 2 + 2 * ", 8)]
#[case("2 * 2 / 2", "2 2 * 2 / ", 2)]
#[case("2 * (2 / 2)", "2 2 2 / * ", 2)]
fn basic(
    #[case] inp: &str,
    #[case] expected_rpn: &str,
    #[case] expected_result: i64,
) -> Result<(), anyhow::Error> {
    let line = inp.to_string();

    let tokens = tokenize(&line)?;
    let rpn = parse(tokens)?;
    let rpn_string = tokens_to_string(&rpn)?;
    assert_eq!(rpn_string, expected_rpn);

    let evaluated = eval(&rpn)?;
    assert_eq!(evaluated, expected_result);

    Ok(())
}

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
