struct MyStruct {
    a: i32,
    b: i32,
    c: i32,
}

fn main() {
    let MyStruct { a, b, c } = MyStruct { a: 1, b: 2, c: 3 };

    let MyStruct { a, .. } = MyStruct { a: 1, b: 2, c: 3 };

    let (.., a, b) = (1, 2, 3, 4, 5);

    if let Some(a) = Option::Some(123) {
        println!("Some({})", a);
    }
}
