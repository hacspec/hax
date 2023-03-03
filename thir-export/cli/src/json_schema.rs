mod export_schema_to;
use thir_export;

fn main() {
    match std::env::args().collect::<Vec<_>>().as_slice() {
        [_, destination] => {
            let destination = thir_export::PathOrDash::from(std::ffi::OsStr::new(destination));
            export_schema_to::export_schema_to(&destination)
        }
        [bin, _rest @ ..] => {
            eprintln!("Usage: {} OUTPUT_FILE", bin);
            std::process::exit(1)
        }
        _ => panic!(),
    }
}
