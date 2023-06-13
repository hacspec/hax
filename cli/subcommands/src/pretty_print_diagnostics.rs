//! This binary is useful for the engine: from OCaml we need to pretty
//! print Hax-errors so that we can inline those as failed items or
//! failed expressions in the generated modules.

//! Thus, this binary expects a JSON diagnostics error on its stdin
//! and outputs on stdout its pretty, `Display`ed version.

#![feature(rustc_private)]
extern crate rustc_driver;

use hax_diagnostics::Diagnostics as D;
use serde_json::{from_reader, Value};

fn main() {
    println!("{}", from_reader::<_, D<Value>>(std::io::stdin()).unwrap())
}
