fn main() {
    let p1 = Box::new(123);

    let p2 = p1;

    drop(p1);

    println!("{}", *p2);

    drop(p2);
}
