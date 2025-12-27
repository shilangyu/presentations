fn add_str(string: &mut String) {
    string.push_str(":)");
}

fn main() {
    let mut my_name = "Marcin".to_string();

    add_str(&mut my_name);
}
