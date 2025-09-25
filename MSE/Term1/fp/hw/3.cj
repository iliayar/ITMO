// S === \x y z. x z (y z)
// S : (a -> b -> c) -> (a -> b) -> a -> c

func S<A, B, C>(x: (A) -> (B) -> C): ((A) -> B) -> (A) -> C {
    { y: (A) -> B => { z: A => x(z)(y(z)) } }
}

main() {
    let unit = S<String, Int, Unit> { _: String => { _: Int => () } }({ _: String => 0 })("")
    println(unit)
}
