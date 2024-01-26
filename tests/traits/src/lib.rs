#![allow(dead_code)]

pub trait SuperTrait: Clone {
    fn function_of_super_trait(self) -> u32;
}

pub trait Foo {
    type AssocType: SuperTrait;
    const N: usize;
    fn assoc_f() -> ();
    fn method_f(&self) -> ();
}

impl SuperTrait for i32 {
    fn function_of_super_trait(self) -> u32 {
        self.abs() as u32
    }
}

impl Foo for () {
    type AssocType = i32;
    const N: usize = 32;
    fn assoc_f() {
        ()
    }
    fn method_f(&self) {
        Self::assoc_f()
    }
}

fn f<T: Foo>(x: T) {
    T::assoc_f();
    x.method_f()
}

fn g<T: Foo>(x: T::AssocType) -> u32 {
    x.function_of_super_trait()
}

struct Struct;

trait Bar<'a> {
    fn bar(self);
}

impl<'a> Struct {
    fn method<T: Bar<'a>>(x: T) {
        x.bar()
    }
}

// Test trait implementations
// XXX: All functions from here on fail with "the frontend could not resolve using `select_trait_candidate`."
pub(crate) type U8 = u8;
pub struct Bytes(Vec<U8>);

impl From<Vec<u8>> for Bytes {
    fn from(x: Vec<u8>) -> Bytes {
        Bytes(x.into_iter().map(|x| x.into()).collect())
    }
}

impl Bytes {
    pub fn declassify(&self) -> Vec<u8> {
        self.0.iter().map(|&x| x).collect()
    }

    pub fn from_hex(s: &str) -> Bytes {
        let s: String = s.split_whitespace().collect();
        if s.len() % 2 == 0 {
            Bytes(
                (0..s.len())
                    .step_by(2)
                    .map(|i| {
                        s.get(i..i + 2)
                            .and_then(|sub| (u8::from_str_radix(sub, 16).ok()))
                    })
                    .collect::<Option<Vec<U8>>>()
                    .expect("Not a hex string1"),
            )
        } else {
            unreachable!("Not a hex string2")
        }
    }
}

pub fn random_bytes(len: usize) -> Vec<u8> {
    (0..len).map(|i| i as u8).collect::<Vec<u8>>()
}
