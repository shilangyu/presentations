#![feature(half_open_range_patterns)]
#![feature(exclusive_range_pattern)]

fn main() {
    let amount = 132;

    let translated = match amount {
        0 | 2.. => "tables",
        1 => "table",
        ..0 => "huh?",
    };

    println!("there are {} {}", amount, translated);
}
