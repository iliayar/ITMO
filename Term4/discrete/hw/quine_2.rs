fn main() {
    let (s1, s2) = ("fn main() {\n    let (s1, s2) = (", ");\n    println!(\"{}{}{}\", s1, &format!(\"{:?}, {:?}\", s1, s2), s2);\n}\n");
    println!("{}{}{}", s1, &format!("{:?}, {:?}", s1, s2), s2);
}
