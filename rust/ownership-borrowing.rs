fn greet(name: &String) {
    println!("Hello, {}", name);
}

fn main() {
    let my_name = "Marcin".to_string();

    greet(&my_name);

    let copy_cat = &my_name;

    println!("{}", my_name);
    println!("{}", copy_cat);
}
