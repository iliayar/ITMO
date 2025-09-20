fn main() {
    let (s1, s2) = ("fn main() {\n    let (s1, s2) = (", ");\n    print!(\"{}{:?}, {:?}{}\", s1, s1, s2, s2);\n}\n");
    print!("{}{:?}, {:?}{}", s1, s1, s2, s2);
}
