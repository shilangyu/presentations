#[derive(Debug, Clone, Default)]
struct MyStruct {
    pub public_field: i32,
    private_field: i32,
    point: Point,
}

struct Point(i32, i32);

fn main() {
    let my_struct = MyStruct {
        public_field: 123,
        private_field: 123,
        point: Point(1, 2),
    };
}
