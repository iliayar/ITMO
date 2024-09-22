fn fix<'a, 'b: 'a, T, R>(
    f: &'b impl Fn(Box<dyn Fn(T) -> R + 'a>, T) -> R,
) -> Box<dyn Fn(T) -> R + 'a> {
    return Box::new(move |x| f(fix(f), x));
}

fn main() {
    let factorial: Box<dyn Fn(usize) -> u64> = fix(&|f, x| {
        if x == 0 {
            1
        } else {
            f(x - 1) * (x as u64)
        }
    });

    assert!(factorial(0) == 1);
    assert!(factorial(1) == 1);
    assert!(factorial(2) == 2);
    assert!(factorial(3) == 6);
    assert!(factorial(10) == 3628800);

    println!("Success");
}
