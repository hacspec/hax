#![allow(dead_code)]

pub trait Printable<S> {
    fn stringify(&self) -> S;
}

impl Printable<String> for i32 {
    fn stringify(&self) -> String {
        self.to_string()
    }
}

pub fn print(a: Box<dyn Printable<String>>) {
    println!("{}", a.stringify());
}
