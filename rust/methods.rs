// point.rs

mod point {
    pub struct Point {
        pub x: f32,
        pub y: f32,
    }

    impl Point {
        pub fn new(pos: f32) -> Self {
            Self { x: pos, y: pos }
        }

        pub fn distance(&self) -> f32 {
            f32::sqrt(self.x.powf(2.0) + self.y.powf(2.0))
        }
    }
}

// main.rs

use point::Point;

impl Point {
    fn origin() -> Self {
        Self { x: 0.0, y: 0.0 }
    }

    fn scale(&mut self, scalar: f32) {
        self.x *= scalar;
        self.y *= scalar;
    }
}

fn main() {
    let mut p = Point::new(2.0);

    println!("{}", p.distance());
    println!("{}", Point::distance(&p));
    p.scale(1.7);
}
