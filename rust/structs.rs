#[derive(Debug, Clone, Default)]
struct MyStruct {
    pub public_field: i32,
    private_field: i32,
}

#[derive(Copy, Clone)]
struct Point(i32, i32);

fn main() {
    let my_struct = MyStruct {
        public_field: 123,
        private_field: 123,
    };

    println!("{:?}", my_struct);

    let default = MyStruct::default();

    let deep_copy = my_struct.clone();

    let p1 = Point(42, 27);
    let p2 = p1;

    println!("{}", p1.0 + p2.1);
}
