use hax_diagnostics::Diagnostics as D;
use serde_json::{from_reader, Value};

fn main() {
    println!("{}", from_reader::<_, D<Value>>(std::io::stdin()).unwrap())
}
