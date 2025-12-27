use std::thread;

fn main() {
    let s = "rust".to_string();

    let handle = thread::spawn(|| {
        println!("{}", s);
    });

    handle.join().unwrap();
}
