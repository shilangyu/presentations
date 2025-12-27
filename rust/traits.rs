trait ToString {
    fn to_string(&self) -> String;
}

struct Point {
    x: i32,
    y: i32,
}

impl ToString for Point {
    fn to_string(&self) -> String {
        format!("Point({}, {})", self.x, self.y)
    }
}

fn print(obj: impl ToString) {
    println!("{}", obj.to_string());
}

fn main() {
    print(Point { x: 0, y: 1 });
}
