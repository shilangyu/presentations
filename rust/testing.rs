pub fn unsafe_divide(numerator: i32, denominator: i32) -> i32 {
    safe_divide(numerator, denominator).unwrap()
}

fn safe_divide(numerator: i32, denominator: i32) -> Result<i32, &'static str> {
    match denominator {
        0 => Err("Cannot divide by zero"),
        _ => Ok(numerator / denominator),
    }
}

#[test]
fn test_safe_divide() {
    assert_eq!(safe_divide(16, 5), Ok(3));
    assert_eq!(safe_divide(16, 0), Err("Cannot divide by zero"));
}
