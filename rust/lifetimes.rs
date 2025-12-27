fn longer<'a>(a: &'a String, b: &'a String) -> &'a String {
    if a.len() > b.len() {
        a
    } else {
        b
    }
}

fn main() {
    let s1 = "hello".to_string();

    let result = {
        let s2 = "rust".to_string();

        longer(&s1, &s2)
    };
}
