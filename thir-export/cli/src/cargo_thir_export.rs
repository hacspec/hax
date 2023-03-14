#![feature(iter_intersperse)]

use clap::Parser;
use cli_lib::{export_schema_to, options, options::NormalizePaths, run};
use std::process::Command;
use thir_export;

fn main() {
    let args = cli_lib::get_args("thir-export");

    std::process::exit(run(options::thir_export_part::All::parse_from(args.iter())
        .normalize_paths()
        .into()));
}
