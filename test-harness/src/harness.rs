mod command_circus_ext;
use command_circus_ext::*;
use serde_json::Value;
use std::process::{Command, Stdio};

#[derive(Clone, Debug)]
pub enum TestKind {
    Translate { backend: String },
    Lint { linter: String },
}

impl TestKind {
    fn as_subcommands(&self) -> [String; 2] {
        match self {
            TestKind::Lint { linter } => ["lint".to_string(), linter.clone()],
            TestKind::Translate { backend } => ["into".to_string(), backend.clone()],
        }
    }
}

#[derive(Clone, Debug, serde::Serialize)]
pub struct TestSpec {
    /// a slow test can be made optional
    pub optional: bool,
    /// a broken test a test that should succeed (or fail) but does
    /// not dues to a bug to be fixed (see field [issue_id] below)
    pub broken: bool,
    /// Github issue ID
    pub issue_id: Option<u64>,
    /// Is that a positive or a negative test?
    pub positive: bool,
}
impl From<Value> for TestSpec {
    /// Parse a JSON value into a TestSpec
    fn from(o: Value) -> Self {
        let as_bool = |key: &str, default: bool| {
            let b = &o[key];
            if b.is_null() {
                default
            } else {
                b.as_bool().unwrap()
            }
        };
        Self {
            optional: as_bool("optional", false),
            positive: as_bool("positive", true),
            broken: as_bool("broken", false),
            issue_id: o["issue_id"].as_u64(),
        }
    }
}

/// The information for a test is given by `cargo metadata`
#[derive(Clone, Debug)]
pub struct TestInfo {
    pub name: String,
    pub manifest: std::path::PathBuf,
    pub description: Option<String>,
}

#[derive(Clone, Debug)]
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
        let mut cmd = Command::circus(&["-C"]);
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
            s.replace(r"\", "/")
                .replace(&workspace, "WORKSPACE_ROOT")
                .replace("Blocking waiting for file lock on build directory", "")
                .trim()
                .to_string()
        };
        let serr = cleanup(String::from_utf8_lossy(&out.stderr).to_string());
        let sout = cleanup(String::from_utf8_lossy(&out.stdout).to_string());

        // 3. make sure the test is successful
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
            (false, (false, false) | (true, true)) => {
                #[derive(serde::Serialize)]
                struct Output {
                    serr: String,
                    sout: String,
                    exit: i32,
                }
                let exit = out.status.code().unwrap_or(std::i32::MAX);
                let out = &Output { serr, sout, exit };
                let name = format!(
                    "{}+{}",
                    self.info.name,
                    self.kind.as_subcommands().join("-")
                );
                insta::with_settings!({
                    info => &self.spec,
                }, { Ok(insta::assert_toml_snapshot!(name, out)) })
            }
            (false, (false, true)) => err("failed, but this is a negative test marked broken")?,
            (false, (true, false)) => err("failed")?,
            (true, (true, false) | (false, true)) => Ok(()),
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
/// [workspace.circus-tests], this function returns a list of tests
fn parse_circus_tests_metadata(info: TestInfo, metadata: &Value) -> Vec<Test> {
    metadata
        .as_object()
        .expect("Expected value at key [circus-tests] to be a dictionary")
        .into_iter()
        .flat_map(|(a, o)| {
            o.as_object()
                .expect(format!("Expected value at key [{}] be a dictionary", a).as_str())
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
                _ => panic!("unexpected metadata [circus-tests.{}.{}]", a, b),
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
                parse_circus_tests_metadata(
                    TestInfo {
                        name: o.name,
                        description: o.description,
                        manifest: o.manifest_path.into(),
                    },
                    &o.metadata["circus-tests"],
                )
            })
            .map(|test| test.into_trial(&workspace_root))
            .collect(),
    )
    .exit();
}
