#[derive(Debug)]
enum Optional<T> {
    Some(T),
    None,
}

impl<T> Default for Optional<T> {
    fn default() -> Self {
        Self::None
    }
}

fn find_user(id: i32) -> Optional<&'static str> {
    use Optional::*;

    if id == 123 {
        return Some("John");
    } else {
        return None;
    }
}

fn main() {
    println!("{:?}", find_user(123));
    println!("{:?}", find_user(321));
    println!("{:?}", Optional::<i32>::default());
}
