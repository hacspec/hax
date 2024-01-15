const OCAML_MODULE: &str = include_str!(concat!(env!("OUT_DIR"), "/module.ml"));

fn main() {
    println!("{}", OCAML_MODULE);
}
