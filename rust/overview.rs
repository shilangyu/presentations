use std::ops::Range;

pub fn double(x: i32) -> i32 {
    x * 2
}

fn main() {
    let num = 123;
    let double_num = double(num);

    let mut other = 123;
    other *= 2;

    let other = "hello";

    for c in other.chars() {
        println!("{}", c);
    }

    let digits = 0..=9;
    let digits = 0..10;

    if digits.contains(&5) || Range::contains(&digits, &5) {
        println!("5 is a digit");
    }

    let big = {
        let small = 3f64;
        small * 100_000.0
    };

    let prefix = if big > 1e9 { "G" } else { "huh?" };

    let tuple = (1, 2, 3);
    println!("{}", tuple.0);

    let (_, _) = (1, 2);
}
