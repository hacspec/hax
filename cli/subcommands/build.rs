fn rustc_version_env_var() {
    let (_version, channel, date) = version_check::triple().unwrap();
    println!("cargo:rustc-env=HAX_RUSTC_VERSION={channel}-{date}");

    let rust_toolchain_file = include_str!("rust-toolchain.toml")
        .parse::<toml::Table>()
        .unwrap();
    println!(
        "cargo:rustc-env=HAX_TOOLCHAIN={}",
        rust_toolchain_file["toolchain"]["channel"]
            .as_str()
            .expect("Could not find key [toolchain.channel] in [rust-toolchain.toml]")
    );
}

fn json_schema_static_asset() {
    let schema = schemars::schema_for!((
        hax_frontend_exporter::Item<hax_frontend_exporter::ThirBody>,
        hax_types::cli_options::Options,
        hax_types::diagnostics::Diagnostics,
        hax_types::engine_api::EngineOptions,
        hax_types::engine_api::Output,
        hax_types::engine_api::WithDefIds<hax_frontend_exporter::ThirBody>,
        hax_types::engine_api::protocol::FromEngine,
        hax_types::engine_api::protocol::ToEngine,
        hax_lib_macros_types::AttrPayload,
    ));
    serde_json::to_writer(
        std::fs::File::create(format!("{}/schema.json", std::env::var("OUT_DIR").unwrap()))
            .unwrap(),
        &schema,
    )
    .unwrap();
}

fn git_dirty_env_var() {
    println!("cargo:rurun-if-env-changed=HAX_GIT_IS_DIRTY");
    let dirty = {
        use std::process::Command;
        let _ = Command::new("git")
            .args(["update-index", "-q", "--refresh"])
            .status();
        !Command::new("git")
            .args(["diff-index", "--quiet", "HEAD", "--"])
            .status()
            .map(|status| status.success())
            .unwrap_or(true)
    };
    println!("cargo:rustc-env=HAX_GIT_IS_DIRTY={}", dirty);
}

fn main() {
    rustc_version_env_var();
    json_schema_static_asset();
    git_dirty_env_var();
}
