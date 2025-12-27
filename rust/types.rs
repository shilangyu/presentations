fn main() {
    let integers: (i8, i16, i32, i64, i128, isize) = (0, 0, 0, 0, 0, 0);
    let naturals: (u8, u16, u32, u64, u128, usize) = (0, 0, 0, 0, 0, 0);
    let boolean: bool = true;
    let character: char = '😸';
    let array: [i32; 3] = [1, 2, 3];
    let array_init: [i32; 3] = [0; 3];
    let unit: () = ();
    let closure = |x| x * 2;

    closure(integers.0);

    let never: ! = return;
}
