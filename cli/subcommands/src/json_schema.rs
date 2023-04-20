const JSON_SCHEMA: &str = include_str!(concat!(env!("OUT_DIR"), "/schema.json"));

fn main() {
    println!("{}", JSON_SCHEMA);
}
