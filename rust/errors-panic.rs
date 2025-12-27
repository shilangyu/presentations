fn main() {
    panic!("Panic thread {:?}!", std::thread::current().id());
}
