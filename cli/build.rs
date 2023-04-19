use toml::Table;

fn main() {
    let (_version, channel, date) = version_check::triple().unwrap();
    println!("cargo:rustc-env=CIRCUS_RUSTC_VERSION={channel}-{date}");

    let rust_toolchain_file = include_str!("../rust-toolchain.toml")
        .parse::<Table>()
        .unwrap();
    println!(
        "cargo:rustc-env=CIRCUS_TOOLCHAIN={}",
        rust_toolchain_file["toolchain"]["channel"]
            .as_str()
            .expect("Could not find key [toolchain.channel] in [rust-toolchain.toml]")
    );
}
