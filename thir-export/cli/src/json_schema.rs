use thir_export::utils::export_schema_to;

fn main() {
    match std::env::args().collect::<Vec<_>>().as_slice() {
        [_, destination] => export_schema_to(destination),
        [bin, _rest @ ..] => {
            println!("Usage: {} OUTPUT_FILE", bin);
            std::process::exit(1)
        }
        _ => panic!(),
    }
}
