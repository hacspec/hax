//! The Lean backend as an external pipeline: `cargo hax into lean` on every
//! generated package, then one Lean workspace whose two `lake build` passes
//! decide `elaborates` and `checked`.

use std::{
    collections::{HashMap, HashSet},
    fs,
    path::{Path, PathBuf},
    sync::Mutex,
};

use anyhow::{Context as _, Result, bail};
use futures::future::BoxFuture;
use hax_types::{
    cli_options::BackendName,
    diagnostics::message::{HaxMessage, ResolvedValue},
};

use super::{
    package::FlsContext,
    runner::{PipelinePhase, PipelineSteps, ToolVersions},
    stage::{LEAN, Stage},
    test::FlsTest,
};
use crate::{
    commands::{HaxEngineOutput, OutMsg},
    log::{JobKind, ReportMessage},
};

pub struct Lean {
    /// The Lean workspace shared by all tests.
    workspace: PathBuf,
    /// The cargo target directory shared by all generated packages, so that
    /// `hax-lib` and its dependencies compile once.
    target_dir: PathBuf,
    /// `hax-lib/proof-libs/lean`, required by the workspace by path.
    proof_lib: PathBuf,
    /// The Lean library name of each successful extraction of this run, by test path.
    libs: Mutex<HashMap<String, String>>,
    /// The tests of this run without a guard library, which fail `checked`.
    unguarded: Mutex<HashSet<String>>,
    /// The rev of the aeneas Lean library the workspace requires, set from
    /// the tool versions. A generated package pins it to the version of the
    /// aeneas binary, overriding the pin of `proof-libs/lean`; a
    /// path-resolved aeneas has no version, and the workspace keeps that pin.
    aeneas_rev: Mutex<Option<String>>,
}

const AENEAS_REPO: &str = "https://github.com/cryspen/aeneas";

/// The stage decided by the `lake build` of the extractions.
fn elaborates() -> Stage {
    LEAN.stage("elaborates")
}

/// The stage decided by the `lake build` of the guard files.
fn checked() -> Stage {
    LEAN.stage("checked")
}

impl Lean {
    pub fn new(ctx: &FlsContext) -> Result<Self> {
        let proof_lib = ctx
            .hax_lib
            .join("proof-libs")
            .join("lean")
            .canonicalize()
            .context("cannot resolve `hax-lib/proof-libs/lean`")?;
        Ok(Self {
            workspace: ctx.fls_cache.join("lean-workspace"),
            target_dir: ctx.fls_cache.join("target"),
            proof_lib,
            libs: Mutex::new(HashMap::new()),
            unguarded: Mutex::new(HashSet::new()),
            aeneas_rev: Mutex::new(None),
        })
    }

    /// The Lean package `cargo hax into lean` scaffolds in a generated package.
    fn lean_dir(&self, ctx: &FlsContext, test: &FlsTest) -> PathBuf {
        ctx.package_dir(test).join("proofs").join("lean")
    }

    fn lib_name(&self, test: &FlsTest) -> Option<String> {
        self.libs.lock().unwrap().get(&test.path).cloned()
    }

    fn guards_dir(&self) -> PathBuf {
        self.workspace.join("guards")
    }

    /// The revision of the aeneas Lean library pinned by the lakefile of
    /// `proof-libs/lean`.
    fn proof_lib_aeneas_rev(&self) -> Result<String> {
        let lakefile = fs::read_to_string(self.proof_lib.join("lakefile.toml"))?;
        regex::Regex::new(r#"(?s)name = "aeneas".*?rev = "([0-9a-f]+)""#)
            .unwrap()
            .captures(&lakefile)
            .map(|c| c[1].to_string())
            .context("no aeneas revision pinned in the lakefile of `proof-libs/lean`")
    }

    async fn extract(&self, ctx: &FlsContext, test: &FlsTest, job: JobKind) -> Result<Stage> {
        let dir = ctx.generate_package(test)?;
        // A previous extraction leaves hand-editable files (the `Assumptions`
        // module) that `cargo hax` does not overwrite; a stale one would
        // change the stage of a renamed item.
        let _ = fs::remove_dir_all(self.lean_dir(ctx, test));

        let mut command = tokio::process::Command::new("cargo");
        command
            .args(["hax", "--message-format", "json", "into", "lean"])
            .current_dir(&dir)
            .env("CARGO_TARGET_DIR", &self.target_dir);
        let output = HaxEngineOutput::from_output(&command.output().await?)?;
        output.report_stderr_and_stdout(job.clone());

        // A `GenericError` names the tool that failed only through the `Step`
        // active when it arrives; aeneas reports partial files even when it
        // fails, so the error decides before any `ProducedFile`.
        let mut last_step: Option<String> = None;
        let mut error: Option<(String, Option<String>)> = None;
        let mut lib = None;
        for message in &output.messages {
            if let OutMsg::Hax(message) = message {
                match message {
                    HaxMessage::Step { target, .. } => last_step = Some(target.clone()),
                    HaxMessage::GenericError { message } => {
                        error.get_or_insert_with(|| (message.clone(), last_step.clone()));
                    }
                    HaxMessage::ProducedFile { path, .. } => {
                        // `<lean_dir>/<Lib>/Extraction/<Module>.lean`
                        let dir = path.parent();
                        if dir
                            .and_then(Path::file_name)
                            .is_some_and(|n| n == "Extraction")
                        {
                            lib = dir
                                .and_then(Path::parent)
                                .and_then(Path::file_name)
                                .map(|n| n.to_string_lossy().into_owned());
                        }
                    }
                    _ => {}
                }
            }
        }
        let stage = if error.is_some() || output.error_code != 0 {
            let (message, step) = error.unwrap_or_else(|| {
                let message = format!(
                    "`cargo hax into lean` exited with code {}",
                    output.error_code
                );
                (message, last_step)
            });
            // Only a failure of charon or aeneas rejects the test; any other
            // failure, such as a tool download, fails the run.
            let stage = match step.as_deref() {
                Some("charon") => LEAN.stage("charon-rejected"),
                Some(step) if step.starts_with("aeneas on ") => LEAN.stage("aeneas-rejected"),
                _ => bail!(
                    "`cargo hax into lean` failed on `{}` outside of charon and aeneas: {message}",
                    test.path
                ),
            };
            job.report_message(message);
            stage
        } else {
            LEAN.stage("extracted")
        };
        job.report_message(format!("stage: {}", stage.as_str()));
        if stage == LEAN.stage("extracted") {
            match lib {
                Some(lib) => {
                    self.libs.lock().unwrap().insert(test.path.clone(), lib);
                }
                None => job.report_message(
                    "no Lean file reported under `<Lib>/Extraction/`; the test fails `elaborates`",
                ),
            }
        }
        Ok(stage)
    }

    /// Writes the lakefile of the workspace: one library per extracted test
    /// pointing at its extraction directory, and one guard library per
    /// extracted test whose guard file can be generated.
    fn assemble_workspace(
        &self,
        ctx: &FlsContext,
        tests: &[&FlsTest],
        job: &JobKind,
    ) -> Result<()> {
        let guards = self.guards_dir();
        fs::create_dir_all(&guards)?;
        let mut lakefile = r#"# Generated by the test driver for the FLS suite; do not edit.
name = "fls-lean-workspace"
version = "0.1.0"
defaultTargets = []
leanOptions = [{ name = "maxErrors", value = "10000" }]
"#
        .to_string();
        lakefile += &self.requires();
        for test in tests {
            let Some(lib) = self.lib_name(test) else {
                continue;
            };
            let lean_dir = self.lean_dir(ctx, test);
            lakefile += &format!(
                "\n[[lean_lib]]\nname = \"{lib}\"\nsrcDir = \"{}\"\n",
                lean_dir.display()
            );
            match self.guard_file(test, &lib, &lean_dir) {
                Ok(guard) => {
                    lakefile +=
                        &format!("\n[[lean_lib]]\nname = \"{lib}Guard\"\nsrcDir = \"guards\"\n");
                    fs::write(guards.join(format!("{lib}Guard.lean")), guard)?;
                }
                Err(e) => {
                    job.report_message(format!("{e:#}; `{}` fails `checked`", test.path));
                    self.unguarded.lock().unwrap().insert(test.path.clone());
                }
            }
        }
        fs::write(self.workspace.join("lakefile.toml"), lakefile)?;
        fs::copy(
            self.proof_lib.join("lean-toolchain"),
            self.workspace.join("lean-toolchain"),
        )?;
        Ok(())
    }

    /// One `#guard` per `equiv` function, with the Lean name looked up in the
    /// extracted `Funs.lean` since aeneas renames namespaces.
    fn guard_file(&self, test: &FlsTest, lib: &str, lean_dir: &Path) -> Result<String> {
        let mut file = format!("import {lib}.Extraction\n");
        if test.equiv.is_empty() {
            return Ok(file);
        }
        let funs_path = lean_dir.join(lib).join("Extraction").join("Funs.lean");
        let funs = fs::read_to_string(&funs_path)
            .with_context(|| format!("cannot read {}", funs_path.display()))?;
        let namespace = regex::Regex::new(r"(?m)^namespace (\S+)")
            .unwrap()
            .captures(&funs)
            .map(|c| c[1].to_string())
            .with_context(|| format!("no namespace in {}", funs_path.display()))?;
        for equiv in &test.equiv {
            let qualified = equiv
                .module_path
                .iter()
                .map(|m| format!("{m}."))
                .chain(std::iter::once(equiv.name.clone()))
                .collect::<String>();
            let re = regex::Regex::new(&format!(
                r"(?m)^(divergent\s+)?def\s+{}\s",
                regex::escape(&qualified)
            ))
            .unwrap();
            if !re.is_match(&funs) {
                bail!(
                    "equiv function `{qualified}` of `{}` has no definition in {}",
                    test.path,
                    funs_path.display()
                );
            }
            file += &format!("#guard ({namespace}.{qualified}).reducesTo true\n");
        }
        Ok(file)
    }

    /// The `[[require]]` blocks of the workspace lakefile.
    fn requires(&self) -> String {
        let mut requires = String::new();
        // Before `hax`, as in a generated package.
        if let Some(rev) = &*self.aeneas_rev.lock().unwrap() {
            requires += &format!(
                "\n[[require]]\nname = \"aeneas\"\ngit = \"{AENEAS_REPO}\"\nrev = \"{rev}\"\nsubDir = \"backends/lean\"\n"
            );
        }
        requires += &format!(
            "\n[[require]]\nname = \"hax\"\npath = \"{}\"\n",
            self.proof_lib.display()
        );
        requires
    }

    fn lake(&self) -> tokio::process::Command {
        let mut command = tokio::process::Command::new("lake");
        // Lake disables its build caches when `CI` is set.
        command.current_dir(&self.workspace).env_remove("CI");
        command
    }

    async fn run_lake(&self, args: &[&str], job: &JobKind) -> Result<(i32, String)> {
        let out = self.lake().args(args).output().await?;
        let text = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        job.report(ReportMessage::Stdout(text.clone()));
        Ok((
            out.status
                .code()
                .context("no exit code: was `lake` killed?")?,
            text,
        ))
    }

    /// Fetches and builds the dependencies of the workspace: the aeneas and
    /// hax Lean libraries with Mathlib below them. They are fetched again
    /// whenever the requirements of the workspace or the lakefile or manifest
    /// of `proof-libs/lean` change; the stamp records them after a complete
    /// fetch.
    async fn prepare_workspace(&self, job: &JobKind) -> Result<()> {
        let stamp_path = self.workspace.join("dependencies.stamp");
        let mut stamp = self.requires();
        for file in ["lakefile.toml", "lake-manifest.json"] {
            let path = self.proof_lib.join(file);
            stamp += &fs::read_to_string(&path)
                .with_context(|| format!("cannot read {}", path.display()))?;
        }
        if fs::read_to_string(&stamp_path).ok().as_ref() != Some(&stamp) {
            let _ = fs::remove_file(&stamp_path);
            let (code, text) = self.run_lake(&["update"], job).await?;
            if code != 0 {
                bail!("`lake update` failed:\n{text}")
            }
            let (code, text) = self.run_lake(&["exe", "cache", "get"], job).await?;
            if code != 0 {
                bail!("`lake exe cache get` failed:\n{text}")
            }
            fs::write(&stamp_path, stamp)?;
        }
        let (code, text) = self.run_lake(&["build", "Hax", "CoreModels"], job).await?;
        if code != 0 {
            bail!("`lake build Hax CoreModels` failed:\n{text}")
        }
        Ok(())
    }

    /// Builds the given libraries in one `lake build` and returns the names of
    /// the libraries that failed. Lake keeps building independent libraries
    /// after a failure and names every failed target at the end.
    async fn lake_build(
        &self,
        libs: &[(String, PathBuf)],
        job: &JobKind,
    ) -> Result<HashSet<String>> {
        if libs.is_empty() {
            return Ok(HashSet::new());
        }
        let names: Vec<&str> = libs.iter().map(|(name, _)| name.as_str()).collect();
        let args: Vec<&str> = std::iter::once("build")
            .chain(names.iter().copied())
            .collect();
        let (code, text) = self.run_lake(&args, job).await?;

        let module_failure = regex::Regex::new(r"^✖ \[\d+/\d+\] Building (\S+)").unwrap();
        let lib_error = regex::Regex::new(r"^error: ([A-Za-z0-9_']+): ").unwrap();
        let path_error = regex::Regex::new(r"^error: ([^:\n]+\.lean):\d+:\d+: ").unwrap();
        let by_name = |name: &str| names.iter().find(|n| **n == name).map(|n| n.to_string());
        let guards = self.guards_dir();
        let by_path = |path: &str| {
            let path = self.workspace.join(path);
            libs.iter()
                .find(|(name, dir)| {
                    path.starts_with(dir)
                        && (dir != &guards || path.file_stem().is_some_and(|s| s == name.as_str()))
                })
                .map(|(name, _)| name.clone())
        };
        let mut failed = HashSet::new();
        for line in text.lines() {
            if let Some(c) = module_failure.captures(line) {
                let root = c[1].split('.').next().unwrap_or("");
                failed.extend(by_name(root));
            } else if let Some(c) = lib_error.captures(line) {
                failed.extend(by_name(&c[1]));
            } else if let Some(c) = path_error.captures(line) {
                failed.extend(by_path(&c[1]));
            } else if let Some(target) = line.strip_prefix("- ") {
                failed.extend(by_name(target.trim()));
            }
        }
        if code != 0 && failed.is_empty() {
            bail!("`lake build` failed outside of any test library:\n{text}")
        }
        if code == 0 && !failed.is_empty() {
            bail!("`lake build` succeeded but errors were attributed to {failed:?}:\n{text}")
        }
        job.report_message(format!(
            "{} libraries, {} failed{}",
            libs.len(),
            failed.len(),
            if failed.is_empty() {
                String::new()
            } else {
                format!(": {}", {
                    let mut v: Vec<_> = failed.iter().cloned().collect();
                    v.sort();
                    v.join(", ")
                })
            }
        ));
        Ok(failed)
    }

    /// Runs the `lake build` of one batch stage and maps the failed libraries
    /// back to test paths. A test without the library of the stage fails it.
    async fn run_batch(
        &self,
        ctx: &FlsContext,
        stage: Stage,
        tests: &[&FlsTest],
        job: &JobKind,
    ) -> Result<HashSet<String>> {
        let unguarded = self.unguarded.lock().unwrap().clone();
        let mut failed = HashSet::new();
        let mut libs: Vec<(String, String, PathBuf)> = vec![];
        for test in tests {
            let lib = if stage == elaborates() {
                self.lib_name(test)
                    .map(|lib| (lib, self.lean_dir(ctx, test)))
            } else if stage == checked() {
                self.lib_name(test)
                    .filter(|_| !unguarded.contains(&test.path))
                    .map(|lib| (format!("{lib}Guard"), self.guards_dir()))
            } else {
                bail!(
                    "`{}` is not a batch stage of the Lean backend",
                    stage.as_str()
                )
            };
            match lib {
                Some((lib, dir)) => libs.push((test.path.clone(), lib, dir)),
                None => {
                    failed.insert(test.path.clone());
                }
            }
        }
        let targets: Vec<(String, PathBuf)> = libs
            .iter()
            .map(|(_, lib, dir)| (lib.clone(), dir.clone()))
            .collect();
        let failed_libs = self.lake_build(&targets, job).await?;
        failed.extend(
            libs.into_iter()
                .filter(|(_, lib, _)| failed_libs.contains(lib))
                .map(|(path, _, _)| path),
        );
        Ok(failed)
    }

    async fn tool_versions(&self, ctx: &FlsContext) -> Result<ToolVersions> {
        let cwd = ctx.options.tests_crate_dir();
        let version = tokio::process::Command::new("cargo")
            .args(["hax", "--version"])
            .current_dir(&cwd)
            .output()
            .await?;
        let version = String::from_utf8_lossy(&version.stdout);
        let hax = version
            .lines()
            .find_map(|l| l.trim().strip_prefix("version="))
            .context("cannot parse `cargo hax --version`")?
            .to_string();
        // A build from a checkout reports its commit, which would change the
        // recorded version with every commit; the nix build of CI reports the
        // package version. Record the package version for both. The commit is
        // not compared with the checkout: `hax-types` embeds it only when it
        // is rebuilt, so it can be older than the build.
        let package = env!("CARGO_PKG_VERSION");
        let hax = if hax.starts_with("untagged-git-rev-") || hax == package {
            package.to_string()
        } else {
            bail!(
                "`cargo hax` is version {hax} but the test driver is built from version {package}; use the `cargo-hax` of this checkout"
            )
        };

        let show = tokio::process::Command::new("cargo")
            .args(["hax", "--message-format", "json", "tools", "show"])
            .current_dir(&cwd)
            .output()
            .await?;
        let stdout = String::from_utf8_lossy(&show.stdout);
        let (tools, versions) = stdout
            .lines()
            .filter_map(|l| serde_json::from_str::<HaxMessage>(l).ok())
            .find_map(|m| match m {
                HaxMessage::ToolsShow {
                    tools, versions, ..
                } => Some((tools, versions)),
                _ => None,
            })
            .context("`cargo hax tools show` produced no `ToolsShow` message")?;
        let mut result = vec![("hax".to_string(), hax)];
        let mut aeneas_rev = None;
        for tool in tools.into_iter().chain(versions) {
            let value = match tool.resolved {
                ResolvedValue::Version(v) => {
                    if tool.name == "aeneas" {
                        aeneas_rev = Some(v.clone());
                    }
                    v
                }
                ResolvedValue::Path(p) => format!("path:{p}"),
            };
            result.push((tool.name, value));
        }
        let lean_lib = match &aeneas_rev {
            Some(rev) => rev.clone(),
            None => self.proof_lib_aeneas_rev()?,
        };
        result.push(("aeneas-lean-lib".to_string(), lean_lib));
        *self.aeneas_rev.lock().unwrap() = aeneas_rev;
        Ok(result)
    }
}

impl PipelineSteps for Lean {
    fn backend(&self) -> BackendName {
        BackendName::Lean
    }

    fn phase_name(&self, phase: PipelinePhase) -> String {
        match phase {
            PipelinePhase::Canary => "canary".into(),
            PipelinePhase::Extract => "cargo hax into lean".into(),
            PipelinePhase::Prepare => "workspace dependencies".into(),
            PipelinePhase::Batch(stage) if stage == checked() => "lake build: guards".into(),
            PipelinePhase::Batch(_) => "lake build: extractions".into(),
        }
    }

    fn extract<'a>(
        &'a self,
        ctx: &'a FlsContext,
        test: &'a FlsTest,
        job: JobKind,
    ) -> BoxFuture<'a, Result<Stage>> {
        Box::pin(self.extract(ctx, test, job))
    }

    fn prepare<'a>(
        &'a self,
        ctx: &'a FlsContext,
        tests: &'a [&'a FlsTest],
        job: JobKind,
    ) -> BoxFuture<'a, Result<()>> {
        Box::pin(async move {
            self.assemble_workspace(ctx, tests, &job)?;
            self.prepare_workspace(&job).await
        })
    }

    fn batch_stages(&self) -> Vec<Stage> {
        vec![elaborates(), checked()]
    }

    fn run_batch<'a>(
        &'a self,
        ctx: &'a FlsContext,
        stage: Stage,
        tests: &'a [&'a FlsTest],
        job: JobKind,
    ) -> BoxFuture<'a, Result<HashSet<String>>> {
        Box::pin(async move { self.run_batch(ctx, stage, tests, &job).await })
    }

    fn tool_versions<'a>(&'a self, ctx: &'a FlsContext) -> BoxFuture<'a, Result<ToolVersions>> {
        Box::pin(self.tool_versions(ctx))
    }
}
