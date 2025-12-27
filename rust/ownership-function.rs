fn greet(name: String) -> String {
    println!("Hello, {}", name);

    return name;
}

fn main() {
    let my_name = "Marcin".to_string();

    let my_name = greet(my_name);
}
