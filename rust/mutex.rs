use std::sync::Mutex;

fn print_num(num_mtx: &Mutex<i32>) {
    if let Ok(num) = num_mtx.lock() {
        println!("{}", num);
    }
}

fn main() {
    let num_mtx = Mutex::new(1);

    print_num(&num_mtx);

    println!("{} was printed", num_mtx.lock().unwrap());
}
