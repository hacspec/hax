use serde_json::Value;
use std::process::{Command, Stdio};

/// Instead of depending on `hax_frontend_exporter` (that links to
/// rustc and exposes a huge number of type definitions and their
/// impls), we just inline a small module here that contains the three
/// type definition we need. See the module for complementary
/// informations.
#[path = "../../../frontend/exporter/src/types/def_id.rs"]
mod hax_frontend_exporter_def_id;
use hax_frontend_exporter_def_id::*;

/// Name of the current crate
const HAX_ENGINE_NAMES_CRATE: &str = "hax_engine_names";
/// Path `a::b` needs to be compiled to a OCaml variant name, `::` is
/// replaced with `SEPARATOR`
const SEPARATOR: &str = "__";
/// "Key" for OCaml quoted strings
const ESCAPE_KEY: &str = "hax_escape_ocaml_json";

fn uppercase_first_letter(s: &str) -> String {
    let mut c = s.chars();
    match c.next() {
        None => String::new(),
        Some(f) => f.to_uppercase().collect::<String>() + c.as_str(),
    }
}

fn disambiguator_to_str(disambiguator: u32) -> String {
    if disambiguator == 0 {
        "".into()
    } else {
        format!("_{disambiguator}")
    }
}

fn def_path_item_to_str(path_item: DefPathItem) -> String {
    match path_item {
        DefPathItem::TypeNs(s)
        | DefPathItem::ValueNs(s)
        | DefPathItem::MacroNs(s)
        | DefPathItem::LifetimeNs(s) => s,
        DefPathItem::CrateRoot => "CrateRoot".into(),
        DefPathItem::Impl => "Impl".into(),
        DefPathItem::ForeignMod => "ForeignMod".into(),
        DefPathItem::Use => "Use".into(),
        DefPathItem::GlobalAsm => "GlobalAsm".into(),
        DefPathItem::Closure => "Closure".into(),
        DefPathItem::Ctor => "Ctor".into(),
        DefPathItem::AnonConst => "AnonConst".into(),
        DefPathItem::OpaqueTy => "OpaqueTy".into(),
        DefPathItem::AnonAdt => "AnonAdt".into(),
    }
}

fn disambiguated_def_path_item_to_str(defpath: DisambiguatedDefPathItem) -> String {
    let data = def_path_item_to_str(defpath.data);
    let disambiguator = disambiguator_to_str(defpath.disambiguator);
    format!("{data}{disambiguator}")
}

fn def_id_to_str(DefId { krate, path, .. }: &mut DefId) -> String {
    if krate == HAX_ENGINE_NAMES_CRATE {
        *krate = "rust_primitives".into();
    };
    let path = path
        .clone()
        .into_iter()
        .map(disambiguated_def_path_item_to_str)
        .collect::<Vec<String>>()
        .join(SEPARATOR);
    format!("{}{SEPARATOR}{path}", uppercase_first_letter(&krate))
}

fn reader_to_str(s: String) -> String {
    let json: Value = match serde_json::from_str(&s) {
        Ok(v) => v,
        Err(e) => panic!("error while parsing JSON: {e}\n\nString was: {}", &s),
    };
    let def_ids: Vec<DefId> = serde_json::from_value(json["def_ids"].clone()).unwrap();
    let impl_infos = json["impl_infos"].clone();

    let def_ids = def_ids
        .into_iter()
        .map(|mut did| {
            let krate_name = def_id_to_str(&mut did);
            (serde_json::to_string(&did).unwrap(), krate_name)
        })
        .collect::<Vec<_>>();

    const TAB: &str = "    ";
    let mut result = String::new();
    result += &format!(
        "type name = \n{TAB}  {}\n",
        def_ids
            .iter()
            .map(|(_, def_name)| format!("{def_name}"))
            .collect::<Vec<_>>()
            .join(&format!("\n{TAB}| "))
    );

    result += "\n";
    result += "module Values = struct\n";
    for (json, name) in &def_ids {
        result += &format!("{TAB}let parsed_{name} = Types.parse_def_id (Yojson.Safe.from_string {}{ESCAPE_KEY}|{}|{ESCAPE_KEY}{})\n", "{", json, "}");
    }
    result += "end\n\n";

    result += &format!(
        "let def_id_of: name -> Types.def_id = function\n{TAB}  {}\n\n",
        def_ids
            .iter()
            .map(|(_, n)| format!("{n} -> Values.parsed_{n}"))
            .collect::<Vec<_>>()
            .join(&format!("\n{TAB}| "))
    );

    result += &format!("let impl_infos_json_list = match Yojson.Safe.from_string {}{ESCAPE_KEY}|{}|{ESCAPE_KEY}{} with | `List l -> l | _ -> failwith \"Expected a list of `def_id * impl_infos`\"\n\n", "{", serde_json::to_string(&impl_infos).unwrap(), "}");
    result +=
        &format!("let impl_infos = Base.List.map ~f:(function | `List [did; ii] -> (Types.parse_def_id did, Types.parse_impl_infos ii) | _ -> failwith \"Expected tuple\") impl_infos_json_list");

    result
}

fn target_dir(suffix: &str) -> camino::Utf8PathBuf {
    let metadata = cargo_metadata::MetadataCommand::new().exec().unwrap();
    let mut dir = metadata.target_directory;
    dir.push(suffix);
    dir
}

fn get_json() -> String {
    let mut cmd =
        Command::new(std::env::var("HAX_CARGO_COMMAND_PATH").unwrap_or("cargo-hax".to_string()));
    cmd.args([
        "hax",
        "-C",
        "-p",
        "hax-engine-names",
        "--lib",
        ";",
        "json",
        "--include-extra",
        "-o",
        "-",
    ])
    .stdout(Stdio::piped())
    .stderr(Stdio::piped());

    cmd.env("CARGO_TARGET_DIR", target_dir("hax"));
    for env in ["DYLD_FALLBACK_LIBRARY_PATH", "LD_LIBRARY_PATH"] {
        cmd.env_remove(env);
    }
    let out = cmd.output().unwrap();
    let stdout = String::from_utf8(out.stdout).unwrap();
    let stderr = String::from_utf8(out.stderr).unwrap();
    eprintln!("{}", stderr);
    stdout
}

fn main() {
    std::fs::write(
        format!("{}/module.ml", std::env::var("OUT_DIR").unwrap()),
        reader_to_str(get_json()),
    )
    .unwrap()
}
