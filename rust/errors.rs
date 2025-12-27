fn safe_divide(numerator: i32, denominator: i32) -> Result<i32, &'static str> {
    match denominator {
        0 => Err("Cannot divide by zero"),
        _ => Ok(numerator / denominator),
    }
}

fn main() {
    let num = safe_divide(16, 0).unwrap();

    println!("{}", num);
}
