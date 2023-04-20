fn rustc_version_env_var() {
    let (_version, channel, date) = version_check::triple().unwrap();
    println!("cargo:rustc-env=CIRCUS_RUSTC_VERSION={channel}-{date}");

    let rust_toolchain_file = include_str!("../../rust-toolchain.toml")
        .parse::<toml::Table>()
        .unwrap();
    println!(
        "cargo:rustc-env=CIRCUS_TOOLCHAIN={}",
        rust_toolchain_file["toolchain"]["channel"]
            .as_str()
            .expect("Could not find key [toolchain.channel] in [rust-toolchain.toml]")
    );
}

fn json_schema_static_asset() {
    let schema = schemars::schema_for!((
        circus_frontend_exporter::Item,
        circus_cli_options::Options,
        circus_diagnostics::Diagnostics<circus_frontend_exporter::Span>,
        circus_cli_options_engine::EngineOptions,
        circus_cli_options_engine::Output,
    ));
    serde_json::to_writer(
        std::fs::File::create(format!("{}/schema.json", std::env::var("OUT_DIR").unwrap()))
            .unwrap(),
        &schema,
    )
    .unwrap();
}

fn main() {
    rustc_version_env_var();
    json_schema_static_asset();
}
