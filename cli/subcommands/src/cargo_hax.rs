#![feature(type_changing_struct_update)]

use clap::Parser;
use colored::Colorize;
use hax_cli_options::{Command, NormalizePaths, Options, RustcCommand};
use itertools::Itertools;
use std::collections::hash_set::HashSet;
use std::collections::HashMap;

/// Return a toolchain argument to pass to [cargo]: when the correct nightly is
/// already present, this is None, otherwise we (1) ensure [rustup] is available
/// (2) install the nightly (3) return the toolchain
fn toolchain() -> Option<&'static str> {
    let current_rustc_version = version_check::triple()
        .map(|(_, channel, date)| format!("{channel}-{date}"))
        .unwrap_or("unknown".into());
    if env!("HAX_RUSTC_VERSION") != current_rustc_version {
        const TOOLCHAIN: &str = env!("HAX_TOOLCHAIN");
        // ensure rustup is available
        which::which("rustup").ok().unwrap_or_else(|| {
            println!("Error: {} was not found, but toolchain {} is required while the current toolchain is {}\n\nExiting.", "rustup".bold(), TOOLCHAIN.bold(), current_rustc_version.bold());
            std::process::exit(1)
        });
        // make sure the toolchain is installed
        rustup_toolchain::install(TOOLCHAIN).unwrap();
        // return the correct toolchain
        Some(TOOLCHAIN)
    } else {
        None
    }
}

/// [get_args] is a wrapper of `std::env::args` that strips a possible
/// cargo subcommand. This allows for a binary [BINARY] to be called
/// both with [cargo BINARY args...] and [cargo-BINARY args...].
pub fn get_args(subcommand: &str) -> Vec<String> {
    let mut args: Vec<_> = std::env::args().collect();
    if args.get(1) == Some(&subcommand.to_string()) {
        // we face a call `cargo [subcommand]`: we need to get rid of the first argument
        args = args.into_iter().skip(1).collect();
    }
    args
}

fn check(
    backend: &hax_cli_options::Backend,
    metadata: &cargo_metadata::Metadata,
    pkg_name: &str,
) -> bool {
    use cargo_metadata::PackageId;

    let backend_path: cargo_metadata::camino::Utf8PathBuf =
        ["proofs", format!("{backend}").as_str()].iter().collect();
    let pkg = metadata
        .packages
        .iter()
        .find(|pkg| pkg.name == pkg_name) // FIXME: is this package unique?
        .unwrap()
        .clone();
    let path = pkg.manifest_path.parent().unwrap().join(&backend_path);

    if !path.exists() {
        eprintln!("no {backend} proofs found for package {pkg_name}");
        return false;
    }

    let resolve = metadata.resolve.as_ref().unwrap();
    let mut graph: HashMap<PackageId, HashSet<PackageId>> = HashMap::new();
    for node in &resolve.nodes {
        let _ = graph.insert(
            node.id.clone(),
            node.deps.iter().map(|dep| dep.pkg.clone()).collect(),
        );
    }

    let mut closure: HashSet<PackageId> = HashSet::new();
    let mut queue: Vec<PackageId> = Vec::new();
    queue.push(pkg.id);
    while let Some(cur) = queue.pop() {
        for dep in &graph[&cur] {
            if !closure.contains(dep) {
                closure.insert(dep.clone());
                queue.push(dep.clone());
            }
        }
    }

    let proofs_path = metadata
        .packages
        .iter()
        .filter(|pkg| closure.contains(&pkg.id))
        .map(|pkg| (pkg.name.clone(), pkg.manifest_path.parent().unwrap()))
        .map(|(name, path)| (name, path.join(&backend_path)))
        .filter(|(_, path)| path.exists())
        .map(|(name, path)| format!("{}={}", name, path))
        .intersperse(":".to_string())
        .collect::<String>();

    let hax_backends_dir = std::env::var("HAX_BACKENDS_DIR").unwrap_or_else(|_| {
        let home = std::env::var("HOME").unwrap();
        format!("{}/.hax", home)
    });
    let check_script = format!("{}/{}/check", hax_backends_dir, backend);
    let mut cmd = std::process::Command::new(&check_script);
    let cmd = cmd
        .current_dir(path)
        .env("HAX_PROOFS_PATH", proofs_path)
        .env("HAX_PKG_NAME", pkg_name);

    cmd.status()
        .expect(&format!("failed to execute {}", check_script))
        .success()
}

fn main() {
    let args: Vec<String> = get_args("hax");
    let options: Options<Command> = Options::parse_from(args.iter()).normalize_paths();

    let mut cmd = std::process::Command::new("cargo");
    if let Some(toolchain) = toolchain() {
        cmd.env("RUSTUP_TOOLCHAIN", toolchain);
    }
    cmd.arg("build").args(&options.cargo_flags);

    match options.command {
        Command::RustcCommand(command) => {
            let options: Options<RustcCommand> = Options { command, ..options };
            cmd.env(
                "RUSTC_WORKSPACE_WRAPPER",
                std::env::var("HAX_RUSTC_DRIVER_BINARY")
                    .unwrap_or("driver-hax-frontend-exporter".into()),
            );
            cmd.env(
                hax_cli_options::ENV_VAR_OPTIONS_FRONTEND,
                serde_json::to_string(&options)
                    .expect("Options could not be converted to a JSON string"),
            );
            std::process::exit(cmd.spawn().unwrap().wait().unwrap().code().unwrap_or(254))
        }
        Command::CheckCommand(backend) => {
            // get primary packages from [cargo -Z unstable-options --build-plan]
            cmd.args([
                "-Z".to_string(),
                "unstable-options".to_string(),
                "--build-plan".to_string(),
            ]);
            let output = cmd.output().unwrap();
            let build_plan: serde_json::Value = serde_json::from_slice(&output.stdout[..]).unwrap();
            let mut primary_packages = build_plan["invocations"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|p| {
                    p["env"]
                        .as_object()
                        .unwrap()
                        .contains_key("CARGO_PRIMARY_PACKAGE")
                })
                .map(|p| p["package_name"].as_str().unwrap())
                .unique();

            // get cargo metadata
            let metadata = cargo_metadata::MetadataCommand::new().exec().unwrap();

            // check the primary packages
            if primary_packages.all(|pkg_name| check(&backend, &metadata, pkg_name)) {
                std::process::exit(0)
            } else {
                std::process::exit(1)
            }
        }
    }
}
