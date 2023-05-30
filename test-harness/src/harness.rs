mod command_hax_ext;
use command_hax_ext::*;
use serde_json::{Map, Value};
use std::process::{Command, Stdio};

#[derive(Clone, Debug, serde::Serialize)]
pub enum TestKind {
    Translate { backend: String },
    Lint { linter: String },
}

impl TestKind {
    fn as_subcommands(&self) -> Vec<String> {
        match self {
            TestKind::Lint { linter } => vec!["lint".to_string(), linter.clone()],
            TestKind::Translate { backend } => {
                vec!["into".to_string(), "-o".into(), "-".into(), backend.clone()]
            }
        }
    }
    fn as_name(&self) -> String {
        (match self {
            TestKind::Lint { linter } => ["lint".to_string(), linter.clone()],
            TestKind::Translate { backend } => ["into".to_string(), backend.clone()],
        })
        .join("-")
    }
}

#[allow(dead_code)]
fn bool_true() -> bool {
    true
}

#[derive(Clone, Debug, serde::Serialize)]
pub struct TestSnapshot {
    #[serde(default = "bool_true")]
    pub stderr: bool,
    #[serde(default = "bool_true")]
    pub stdout: bool,
}

#[derive(Clone, Debug, serde::Serialize)]
pub struct TestSpec {
    /// is the test optional? (useful for slow tests for instance)
    pub optional: bool,
    /// a broken test a test that should succeed (or fail) but does
    /// not dues to a bug to be fixed (see field [issue_id] below)
    pub broken: bool,
    /// Github issue ID
    pub issue_id: Option<u64>,
    /// Is that a positive or a negative test?
    pub positive: bool,
    pub snapshot: TestSnapshot,
}
impl From<Value> for TestSpec {
    /// Parse a JSON value into a TestSpec
    fn from(o: Value) -> Self {
        fn as_opt_bool(v: &Value, def: bool) -> Option<bool> {
            if v.is_null() {
                return Some(def);
            }
            v.as_bool()
        }
        fn as_bool(o: &Value, k: &str, def: bool) -> bool {
            let v = &o[k];
            as_opt_bool(v, def)
                .expect(format!("[{}] was expected to be a boolean, got {}", k, v).as_str())
        }
        let snapshot = &o["snapshot"];
        TestSpec {
            optional: as_bool(&o, "optional", false),
            broken: as_bool(&o, "broken", false),
            positive: as_bool(&o, "positive", true),
            issue_id: o["positive"].as_u64(),
            snapshot: as_opt_bool(snapshot, true)
                .map(|b| TestSnapshot {
                    stderr: b,
                    stdout: b,
                })
                .or_else(|| match snapshot.as_str() {
                    Some(v @ ("stdout" | "stderr" | "both" | "none")) => Some(TestSnapshot {
                        stdout: matches!(v, "stdout" | "both"),
                        stderr: matches!(v, "stderr" | "both"),
                    }),
                    Some(v) => panic!(
                        "[snapshot] is \"{}\" but was expected to be \"stderr\", \"stdout\" or \"both\"", v
                    ),
                    None => None,
                })
                .unwrap_or_else(|| TestSnapshot {
                    stderr: as_bool(&snapshot, "stderr", true),
                    stdout: as_bool(&snapshot, "stdout", true),
                }),
        }
    }
}

/// The information for a test is given by `cargo metadata`
#[derive(Clone, Debug, serde::Serialize)]
pub struct TestInfo {
    pub name: String,
    pub manifest: std::path::PathBuf,
    pub description: Option<String>,
}

#[derive(Clone, Debug, serde::Serialize)]
pub struct Test {
    pub kind: TestKind,
    pub info: TestInfo,
    pub spec: TestSpec,
}

impl std::fmt::Display for Test {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} - {:?}", self.info.name, self.kind)?;
        if let Some(issue_id) = self.spec.issue_id {
            write!(f, " #{}", issue_id)?;
        };
        Ok(())
    }
}

impl Test {
    fn into_runner(self, workspace: String) -> Result<(), libtest_mimic::Failed> {
        // 1. cook a command
        let mut cmd = Command::hax(&["-C"]);
        cmd.arg("--manifest-path").arg(self.info.manifest.clone());
        cmd.arg(";");
        cmd.stdout(Stdio::piped()).stderr(Stdio::piped());
        cmd.args(self.kind.as_subcommands());

        // 2. execute it (twice, idea of @franziskuskiefer, so that
        // the messages related to building dependencies are not
        // included in the second one)
        let _ = cmd.output().unwrap();
        let out = cmd.output().unwrap();

        let command_successful = out.status.success();
        let cleanup = |s: String| {
            use lazy_static::lazy_static;
            use regex::Regex;
            lazy_static! {
                // Regex [TIME] matches compile times
                static ref TIME: Regex = Regex::new(r"\bin \d+(\.\d+)?s\b").unwrap();
                static ref LOCK: Regex = Regex::new(r"Blocking waiting for \w+ lock on (the registry index|build directory|package cache)").unwrap();
            }
            TIME.replace_all(
                LOCK.replace_all(
                    &s.replace(r"\", "/").replace(&workspace, "WORKSPACE_ROOT"),
                    "",
                )
                .as_ref(),
                "in XXs",
            )
            .trim()
            .to_string()
        };
        let serr = cleanup(String::from_utf8_lossy(&out.stderr).to_string());
        let sout = String::from_utf8_lossy(&out.stdout).to_string();

        // 3. make sure the test is successful
        let mut snapshot: Map<String, Value> = Map::new();
        if self.spec.snapshot.stderr {
            snapshot.insert("stderr".to_string(), Value::String(serr.clone()));
        }
        if self.spec.snapshot.stdout {
            snapshot.insert(
                "stdout".to_string(),
                serde_json::from_str(&sout)
                    .unwrap_or_else(|_| Value::String(cleanup(sout.clone()))),
            );
        }

        if !snapshot.is_empty() {
            let exit = out.status.code().unwrap_or(std::i32::MAX);
            snapshot.insert("exit".to_string(), exit.into());
            let snapshot = Value::Object(snapshot);
            let name = format!("{} {}", self.info.name, self.kind.as_name());

            insta::with_settings!({
                info => &self,
            }, { insta::assert_toml_snapshot!(name, snapshot) })
        }

        let err = |s: &str| {
            Err(format!(
                "Command {s}.\nThe command was: {:?}{}",
                cmd,
                if command_successful {
                    "".to_string()
                } else {
                    format!("\nSTDOUT:\n{}\nSTDERR:\n{}", sout, serr)
                }
            ))
        };
        match (command_successful, (self.spec.positive, self.spec.broken)) {
            (true, (true, false) | (false, true)) => Ok(()),
            (false, (false, false) | (true, true)) => Ok(()),
            (false, (false, true)) => err("failed, but this is a negative test marked broken")?,
            (false, (true, false)) => err("failed")?,
            (true, (true, true)) => err("succeeded, but this is a positive test marked broken")?,
            (true, (false, false)) => err("succeeded, but this is a negative test")?,
        }
    }

    fn into_trial(&self, workspace: &String) -> libtest_mimic::Trial {
        libtest_mimic::Trial::test(format!("{}", &self), {
            let test = self.clone();
            let workspace = workspace.clone();
            move || test.clone().into_runner(workspace)
        })
        .with_kind(if self.spec.positive {
            "positive"
        } else {
            "negative"
        })
        .with_ignored_flag(self.spec.optional)
    }
}

/// Given [metadata] the table declared in a test's [Cargo.toml]
/// [workspace.hax-tests], this function returns a list of tests
fn parse_hax_tests_metadata(info: TestInfo, metadata: &Value) -> Vec<Test> {
    if metadata.is_null() {
        return vec![];
    }

    metadata
        .as_object()
        .expect(
            format!(
                "Expected value at key [hax-tests] to be a dictionary for package {:#?}",
                info
            )
            .as_str(),
        )
        .into_iter()
        .flat_map(|(a, o)| {
            o.as_object()
                .expect(
                    format!(
                        "Expected value at key [{}] be a dictionary for package {:#?}",
                        a, info
                    )
                    .as_str(),
                )
                .into_iter()
                .flat_map(|(key, o)| key.split("+").map(|k| (k.trim().to_string(), o.clone())))
                .map(|(b, o)| (a.clone(), b, o))
        })
        .map(|(a, b, o)| Test {
            spec: o.into(),
            info: info.clone(),
            kind: match a.as_str() {
                "into" => TestKind::Translate { backend: b },
                "lint" => TestKind::Lint { linter: b },
                _ => panic!(
                    "unexpected metadata [hax-tests.{}.{}] for package {:#?}",
                    a, b, info
                ),
            },
        })
        .collect()
}

fn main() {
    let metadata = cargo_metadata::MetadataCommand::new()
        .manifest_path("../tests/Cargo.toml")
        .exec()
        .unwrap();
    let workspace_root: String = metadata.workspace_root.into();

    libtest_mimic::run(
        &libtest_mimic::Arguments::from_args(),
        metadata
            .packages
            .into_iter()
            .flat_map(|o| {
                parse_hax_tests_metadata(
                    TestInfo {
                        name: o.name,
                        description: o.description,
                        manifest: o.manifest_path.into(),
                    },
                    &o.metadata["hax-tests"],
                )
            })
            .map(|test| test.into_trial(&workspace_root))
            .collect(),
    )
    .exit();
}
