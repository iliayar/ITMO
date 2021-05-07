fn main() {
    let s = "fn main() {\n    let s = ?;\n    let s = str::replacen(s, \"?\", &format!(\"{:?}\", s), 1);\n    println!(\"{}\", s);\n}\n";
    let s = str::replacen(s, "?", &format!("{:?}", s), 1);
    println!("{}", s);
}

