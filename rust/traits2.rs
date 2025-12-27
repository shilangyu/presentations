trait ToString {
    fn to_string(&self) -> String;
}

trait Printable: ToString {
    fn print(&self) {
        println!("{}", self.to_string());
    }
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

impl Printable for Point {}

fn print(obj: impl Printable) {
    obj.print();
}

fn main() {
    print(Point { x: 0, y: 1 });
}
