use std::{any::type_name, fmt::Display};

// or: fn print_default<T: Display + Default>()
fn print_default<T>()
where
    T: Display + Default,
{
    println!(
        "Default value of {} is `{}`",
        type_name::<T>(),
        T::default(),
    );
}

fn main() {
    print_default::<i32>();
    print_default::<String>();
    print_default::<bool>();
}
