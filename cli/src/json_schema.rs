mod common;

use circus_frontend_exporter;
use clap::{Parser, ValueEnum};

#[derive(Parser, Debug, Clone)]
#[command(author, version, about, long_about = None)]
struct Options {
    #[arg(value_enum)]
    kind: Kind,
    destination: circus_frontend_exporter::PathOrDash,
}

#[derive(ValueEnum, Debug, Clone)]
enum Kind {
    Cli,
    Ast,
    Diagnostics,
}

use schemars::{schema::RootSchema, JsonSchema};

macro_rules! wrapped_schema_for {
    ($type:ty) => {{
        #[derive(JsonSchema)]
        struct TypeWrapper {
            #[allow(dead_code)]
            item: $type,
        }
        schemars::schema_for!(TypeWrapper)
    }};
}

fn main() {
    let Options { kind, destination } =
        Options::parse_from(common::get_args("circus-export-json-schemas").iter());
    let schema: RootSchema = match kind {
        Kind::Cli => wrapped_schema_for!(common::options::circus_engine_part::Options),
        Kind::Ast => wrapped_schema_for!(circus_frontend_exporter::Item),
        Kind::Diagnostics => {
            wrapped_schema_for!(circus_diagnostics::Diagnostics<circus_frontend_exporter::Span>)
        }
    };
    serde_json::to_writer(destination.open_or_stdout(), &schema).unwrap();
}
