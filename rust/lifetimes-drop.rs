fn main() {
    let s = "hello".to_string();

    let reference = &s;

    println!("{}", reference);

    drop(s);
}
