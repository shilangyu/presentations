fn dangle() -> &String {
    let s = "rust".to_string();

    return &s;
}

fn main() {
    let s_ref = dangle();

    println!("{}", s_ref);
}
