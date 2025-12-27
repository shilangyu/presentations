fn greet(name: String) {
    println!("Hello, {}", name);
}

fn main() {
    let my_name = "Marcin".to_string();

    greet(my_name);

    println!("{} was greeted", my_name);
}
