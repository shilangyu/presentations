fn main() {
    let a: Option<i32> = Some(1);

    match a {
        Some(val) => println!("{}", val),
        None => println!("no value"),
    }

    match a {
        Some(val) if val > 3 => println!("value is big enough"),
        _ => println!("value is not big enough or not present"),
    }

    match a {
        Some(3) => println!("there is a 3"),
        Some(val @ 4..=10) => println!("there is a value between 4 and 10: {}", val),
        _ => {}
    }
}
