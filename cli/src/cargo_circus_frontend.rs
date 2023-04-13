#![feature(iter_intersperse)]

mod common;

use clap::Parser;
use common::{options, options::NormalizePaths, run};

fn main() {
    let args = common::get_args("circus-frontend-exporter");

    std::process::exit(run(options::circus_frontend_part::All::parse_from(
        args.iter(),
    )
    .normalize_paths()
    .into()));
}
