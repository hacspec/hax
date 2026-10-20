//! End-to-end tests for the Lean package scaffolding: first-run generation,
//! the non-overriding re-run, the clearing of stale extraction files, the
//! recreation of deleted files with its commented-import opt-out, the
//! root-module checks, and the two ways of disabling the scaffolding.

mod common;

use std::path::{Path, PathBuf};

use common::{path_entries, stub_pipeline_tools, write_executable};

/// The shim hax writes to reach the user's models in `Assumptions/`.
const SHIM: &str = "module\n\npublic import MyFixture.Assumptions.FunsExternal\n";

/// A stub aeneas that emulates the extraction: it writes `Types.lean`,
/// `Funs.lean` and the `ProofObligations.lean` template under
/// `<-dest>/<-subdir>/`, keeping the last occurrence of each flag like the
/// real tool. With `externals`, it additionally generates a template for
/// the models of external definitions.
fn extraction_stub(externals: bool) -> String {
    let mut stub = String::from(
        r#"#!/bin/sh
dest=""
subdir=""
while [ $# -gt 0 ]; do
  case "$1" in
    -dest) dest="$2"; shift ;;
    -subdir) subdir="$2"; shift ;;
  esac
  shift
done
mkdir -p "$dest/$subdir"
printf 'def types := 0\n' > "$dest/$subdir/Types.lean"
printf 'def funs := 0\n' > "$dest/$subdir/Funs.lean"
printf 'def obligations := 0\n' > "$dest/$subdir/ProofObligations.lean"
"#,
    );
    if externals {
        stub.push_str(
            r#"printf '%s\n' '-- fill in the external functions' > "$dest/$subdir/FunsExternal_Template.lean""#,
        );
        stub.push('\n');
    }
    stub
}

/// A crate named `my-fixture` (so the dash-to-CamelCase derivation is
/// exercised) with stub tools; the aeneas stub writes extraction files.
fn setup(dir: &Path) -> PathBuf {
    let crate_dir = dir.join("crate");
    common::write_crate(&crate_dir, "my-fixture");
    let bin = dir.join("bin");
    stub_pipeline_tools(&bin, &extraction_stub(false));
    std::fs::write(crate_dir.join("hax.toml"), path_entries(&bin)).unwrap();
    crate_dir
}

fn run_backend(crate_dir: &Path, args: &[&str]) -> (String, bool) {
    common::run_hax(&[&["into", "lean"], args].concat(), crate_dir, &[])
}

fn read(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap()
}

#[test]
fn first_run_scaffolds_a_complete_package() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = setup(dir.path());

    let (output, success) = run_backend(&crate_dir, &[]);
    assert!(success, "{output}");

    let lean_dir = crate_dir.join("proofs/lean");
    let lakefile = read(&lean_dir.join("lakefile.toml"));
    // The package is named after the crate, the library after the module
    // root.
    assert!(lakefile.contains("name = \"my-fixture\""), "{lakefile}");
    assert!(lakefile.contains("name = \"MyFixture\""), "{lakefile}");
    assert!(lean_dir.join("lean-toolchain").is_file());
    assert_eq!(
        read(&lean_dir.join(".gitignore")),
        "/llbc/\n/.lake/\n/aeneas-error.log\n"
    );
    // The root module imports the aggregate extraction module and the
    // Verification stub; the aggregate imports exactly the files this run
    // produced, in build order, without the ProofObligations template.
    assert_eq!(
        read(&lean_dir.join("MyFixture.lean")),
        "import MyFixture.Extraction\n\
         import MyFixture.Verification.ProofObligations\n"
    );
    assert_eq!(
        read(&lean_dir.join("MyFixture/Extraction.lean")),
        "-- Imports the extraction modules. Rewritten by hax on every extraction.\n\
         module\n\
         \n\
         public import MyFixture.Extraction.Types\n\
         public import MyFixture.Extraction.Funs\n"
    );
    assert!(
        lean_dir
            .join("MyFixture/Verification/ProofObligations.lean")
            .is_file()
    );
    // A freshly scaffolded package is consistent: no root-module warnings.
    assert!(!output.contains("does not import"), "{output}");
    assert!(!output.contains("no longer produces"), "{output}");
}

#[test]
fn a_re_run_clears_stale_extraction_files_but_overwrites_nothing_else() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = setup(dir.path());
    let lean_dir = crate_dir.join("proofs/lean");

    let (output, success) = run_backend(&crate_dir, &[]);
    assert!(success, "{output}");

    // User edits outside Extraction/, and a file the extraction no longer
    // produces inside it.
    let root = lean_dir.join("MyFixture.lean");
    let edited_root = format!("{}-- a user comment\n", read(&root));
    std::fs::write(&root, &edited_root).unwrap();
    let lakefile = lean_dir.join("lakefile.toml");
    let edited_lakefile = format!("{}# a user comment\n", read(&lakefile));
    std::fs::write(&lakefile, &edited_lakefile).unwrap();
    let stale = lean_dir.join("MyFixture/Extraction/Stale.lean");
    std::fs::write(&stale, "def stale := 0\n").unwrap();
    // The aggregate extraction module is hax-owned: edits are overwritten.
    let aggregate = lean_dir.join("MyFixture/Extraction.lean");
    let generated_aggregate = read(&aggregate);
    std::fs::write(&aggregate, "-- an edit\n").unwrap();

    let (output, success) = run_backend(&crate_dir, &[]);
    assert!(success, "{output}");
    assert!(!stale.exists());
    assert!(lean_dir.join("MyFixture/Extraction/Funs.lean").is_file());
    assert_eq!(read(&root), edited_root);
    assert_eq!(read(&lakefile), edited_lakefile);
    assert_eq!(read(&aggregate), generated_aggregate);
    // The default-pin warning for the path-resolved aeneas names the
    // generated lakefile; with the lakefile already on disk, nothing is
    // generated and the warning would be unactionable.
    assert!(
        !output.contains("pinning the aeneas Lean library"),
        "{output}"
    );
}

#[test]
fn deleted_files_come_back_unless_their_import_is_commented_out() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = setup(dir.path());
    let lean_dir = crate_dir.join("proofs/lean");
    let stub_path = lean_dir.join("MyFixture/Verification/ProofObligations.lean");

    let (output, success) = run_backend(&crate_dir, &[]);
    assert!(success, "{output}");

    // Deleted: comes back on the next run.
    std::fs::remove_file(&stub_path).unwrap();
    let (output, success) = run_backend(&crate_dir, &[]);
    assert!(success, "{output}");
    assert!(stub_path.is_file());

    // Commented-out import: the deletion sticks, without warnings.
    let root = lean_dir.join("MyFixture.lean");
    let contents = read(&root).replace(
        "import MyFixture.Verification.ProofObligations",
        "-- import MyFixture.Verification.ProofObligations",
    );
    std::fs::write(&root, contents).unwrap();
    std::fs::remove_file(&stub_path).unwrap();
    let (output, success) = run_backend(&crate_dir, &[]);
    assert!(success, "{output}");
    assert!(!stub_path.exists());
    assert!(!output.contains("does not import"), "{output}");
}

#[test]
fn an_unimported_file_and_a_stale_import_are_warned_about() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = setup(dir.path());
    let lean_dir = crate_dir.join("proofs/lean");
    std::fs::create_dir_all(&lean_dir).unwrap();
    // A pre-existing root module in the pre-aggregate layout: it misses the
    // aggregate extraction module and imports a `Specs` the extraction does
    // not produce. The commented import opts out warning-free.
    std::fs::write(
        lean_dir.join("MyFixture.lean"),
        "import MyFixture.Extraction.Funs\n\
         import MyFixture.Extraction.Specs\n\
         -- import MyFixture.Verification.ProofObligations\n",
    )
    .unwrap();

    let (output, success) = run_backend(&crate_dir, &[]);
    assert!(success, "{output}");
    assert!(
        output.contains("does not import MyFixture.Extraction,"),
        "{output}"
    );
    assert!(
        output.contains("imports MyFixture.Extraction.Specs"),
        "{output}"
    );
    assert!(output.contains("no longer produces"), "{output}");
    assert!(
        !output.contains("MyFixture.Verification.ProofObligations"),
        "{output}"
    );
    // Only the aggregate module is expected to be imported, not the
    // individual extraction files it covers.
    assert!(
        !output.contains("does not import MyFixture.Extraction."),
        "{output}"
    );
}

#[test]
fn external_models_are_seeded_into_assumptions_and_reached_through_a_shim() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = setup(dir.path());
    // A template with the real aeneas header, so the header rewrite is
    // exercised.
    let stub = extraction_stub(false)
        + r#"cat > "$dest/$subdir/FunsExternal_Template.lean" <<'EOF'
-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- This is a template file: rename it to "FunsExternal.lean" and fill the holes.
-- fill in the external functions
EOF
"#;
    write_executable(&dir.path().join("bin/aeneas"), &stub);
    let lean_dir = crate_dir.join("proofs/lean");
    let assumptions = lean_dir.join("MyFixture/Assumptions/FunsExternal.lean");
    let shim = lean_dir.join("MyFixture/Extraction/FunsExternal.lean");
    let template = lean_dir.join("MyFixture/Extraction/FunsExternal_Template.lean");

    let (output, success) = run_backend(&crate_dir, &[]);
    assert!(success, "{output}");
    // Seeded from the aeneas template, with the generated-file banner
    // dropped and the rename instruction replaced; the shim points the
    // generated imports at it.
    assert_eq!(
        read(&assumptions),
        "-- Seeded by hax from Extraction/FunsExternal_Template.lean: fill the holes.\n\
         -- hax never modifies this file; after re-extraction, compare it against the\n\
         -- regenerated template to see what changed.\n\
         -- fill in the external functions\n"
    );
    assert_eq!(read(&shim), SHIM);
    // The template keeps the banner but describes the Assumptions/ workflow
    // instead of instructing a rename.
    let template_contents = read(&template);
    assert!(
        template_contents.contains("AUTOMATICALLY GENERATED"),
        "{template_contents}"
    );
    assert!(
        template_contents.contains("hax seeded MyFixture/Assumptions/FunsExternal.lean"),
        "{template_contents}"
    );
    assert!(
        !template_contents.contains("rename it"),
        "{template_contents}"
    );
    // Neither the shim nor the template is imported by the aggregate
    // extraction module.
    let aggregate = read(&lean_dir.join("MyFixture/Extraction.lean"));
    assert!(!aggregate.contains("FunsExternal"), "{aggregate}");
    assert!(!output.contains("does not import"), "{output}");

    // The user's models survive a re-run; the shim is regenerated.
    std::fs::write(&assumptions, "def models := 0\n").unwrap();
    let (output, success) = run_backend(&crate_dir, &[]);
    assert!(success, "{output}");
    // They are not a Lean module, which the extraction importing them is.
    assert!(output.contains("is not a Lean module"), "{output}");
    assert_eq!(read(&assumptions), "def models := 0\n");
    assert_eq!(read(&shim), SHIM);
}

#[test]
fn external_models_living_in_extraction_are_rescued_before_the_clearing() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = setup(dir.path());
    write_executable(&dir.path().join("bin/aeneas"), &extraction_stub(true));
    let lean_dir = crate_dir.join("proofs/lean");
    // The pre-`Assumptions/` layout: the filled-in models inside
    // `Extraction/`.
    let old = lean_dir.join("MyFixture/Extraction/FunsExternal.lean");
    std::fs::create_dir_all(old.parent().unwrap()).unwrap();
    std::fs::write(&old, "def models := 0\n").unwrap();

    let (output, success) = run_backend(&crate_dir, &[]);
    assert!(success, "{output}");
    assert!(output.contains("moved"), "{output}");
    assert_eq!(
        read(&lean_dir.join("MyFixture/Assumptions/FunsExternal.lean")),
        "def models := 0\n"
    );
    assert_eq!(read(&old), SHIM);
}

/// An external model the rescue cannot read must stop the run: the clearing
/// would delete the file the rescue exists to preserve.
#[test]
fn an_unreadable_external_model_stops_the_run_before_the_clearing() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = setup(dir.path());
    let lean_dir = crate_dir.join("proofs/lean");
    let old = lean_dir.join("MyFixture/Extraction/FunsExternal.lean");
    std::fs::create_dir_all(old.parent().unwrap()).unwrap();
    // Not valid UTF-8, so reading it as a string fails.
    std::fs::write(&old, [0xff, 0xfe, 0x00]).unwrap();

    let (output, success) = run_backend(&crate_dir, &[]);
    assert!(!success, "{output}");
    assert!(output.contains("failed to read"), "{output}");
    // The file the rescue could not handle survives, and aeneas never ran.
    assert!(old.is_file(), "{output}");
    assert!(
        !lean_dir.join("MyFixture/Extraction/Funs.lean").exists(),
        "{output}"
    );
}

#[test]
fn project_files_false_disables_scaffolding_but_not_the_clearing() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = setup(dir.path());
    let hax_toml = crate_dir.join("hax.toml");
    std::fs::write(
        &hax_toml,
        format!("project-files = false\n{}", read(&hax_toml)),
    )
    .unwrap();
    let lean_dir = crate_dir.join("proofs/lean");
    let stale = lean_dir.join("MyFixture/Extraction/Stale.lean");
    std::fs::create_dir_all(stale.parent().unwrap()).unwrap();
    std::fs::write(&stale, "def stale := 0\n").unwrap();

    let (output, success) = run_backend(&crate_dir, &[]);
    assert!(success, "{output}");
    assert!(!lean_dir.join("lakefile.toml").exists());
    assert!(!lean_dir.join("MyFixture.lean").exists());
    assert!(!lean_dir.join("MyFixture/Verification").exists());
    // Extraction/ stays hax-owned: stale files are still cleared, and the
    // aggregate extraction module is still written.
    assert!(!stale.exists());
    assert!(lean_dir.join("MyFixture/Extraction/Funs.lean").is_file());
    assert!(lean_dir.join("MyFixture/Extraction.lean").is_file());
}

#[test]
fn project_files_false_keeps_the_assumptions_wiring() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = setup(dir.path());
    write_executable(&dir.path().join("bin/aeneas"), &extraction_stub(true));
    let hax_toml = crate_dir.join("hax.toml");
    std::fs::write(
        &hax_toml,
        format!("project-files = false\n{}", read(&hax_toml)),
    )
    .unwrap();
    let lean_dir = crate_dir.join("proofs/lean");

    let (output, success) = run_backend(&crate_dir, &[]);
    assert!(success, "{output}");
    // The wiring of external definitions is extraction behavior, not
    // scaffolding: the models are still seeded and reached through the shim.
    assert_eq!(
        read(&lean_dir.join("MyFixture/Assumptions/FunsExternal.lean")),
        "-- fill in the external functions\n"
    );
    assert_eq!(
        read(&lean_dir.join("MyFixture/Extraction/FunsExternal.lean")),
        SHIM
    );
    assert!(!lean_dir.join("lakefile.toml").exists());
}

#[test]
fn an_overridden_subdir_disables_scaffolding_and_the_clearing() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = setup(dir.path());
    let lean_dir = crate_dir.join("proofs/lean");
    let stale = lean_dir.join("MyFixture/Extraction/Stale.lean");
    std::fs::create_dir_all(stale.parent().unwrap()).unwrap();
    std::fs::write(&stale, "def stale := 0\n").unwrap();

    let (output, success) = run_backend(&crate_dir, &["--aeneas-args=-subdir Other/Extraction"]);
    assert!(success, "{output}");
    assert!(output.contains("overrides -subdir"), "{output}");
    assert!(!lean_dir.join("lakefile.toml").exists());
    assert!(!lean_dir.join("MyFixture.lean").exists());
    // hax does not know the layout: nothing is cleared, and the extraction
    // landed where the override says.
    assert!(stale.is_file());
    assert!(lean_dir.join("Other/Extraction/Funs.lean").is_file());
}

#[test]
fn an_overridden_dest_disables_scaffolding_and_the_clearing() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = setup(dir.path());
    let lean_dir = crate_dir.join("proofs/lean");
    let stale = lean_dir.join("MyFixture/Extraction/Stale.lean");
    std::fs::create_dir_all(stale.parent().unwrap()).unwrap();
    std::fs::write(&stale, "def stale := 0\n").unwrap();

    let (output, success) = run_backend(&crate_dir, &["--aeneas-args=-dest elsewhere"]);
    assert!(success, "{output}");
    assert!(output.contains("overrides -dest"), "{output}");
    assert!(!lean_dir.join("lakefile.toml").exists());
    assert!(!lean_dir.join("MyFixture.lean").exists());
    // hax does not know the layout: nothing is cleared, and the extraction
    // landed where the override says.
    assert!(stale.is_file());
    assert!(
        crate_dir
            .join("elsewhere/MyFixture/Extraction/Funs.lean")
            .is_file()
    );
}

#[test]
fn a_handwritten_lakefile_lean_suppresses_the_lakefile_toml() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = setup(dir.path());
    let lean_dir = crate_dir.join("proofs/lean");
    std::fs::create_dir_all(&lean_dir).unwrap();
    let lakefile_lean = lean_dir.join("lakefile.lean");
    std::fs::write(&lakefile_lean, "-- a handwritten lakefile\n").unwrap();

    let (output, success) = run_backend(&crate_dir, &[]);
    assert!(success, "{output}");
    // lake rejects a package with both configuration files; the rest of the
    // scaffolding is unaffected.
    assert!(!lean_dir.join("lakefile.toml").exists());
    assert_eq!(read(&lakefile_lean), "-- a handwritten lakefile\n");
    assert!(lean_dir.join("MyFixture.lean").is_file());
    // No lakefile is generated, so the default-pin warning for the
    // path-resolved aeneas has nothing to point at.
    assert!(
        !output.contains("pinning the aeneas Lean library"),
        "{output}"
    );
}

#[test]
fn a_divergent_external_model_left_in_extraction_is_warned_about() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = setup(dir.path());
    write_executable(&dir.path().join("bin/aeneas"), &extraction_stub(true));
    let lean_dir = crate_dir.join("proofs/lean");
    // The models already live in `Assumptions/`, but `Extraction/` holds a
    // divergent copy (say, edited by mistake): it is not rescued, so the
    // clearing deletes it, which deserves a warning.
    let assumptions = lean_dir.join("MyFixture/Assumptions/FunsExternal.lean");
    std::fs::create_dir_all(assumptions.parent().unwrap()).unwrap();
    std::fs::write(&assumptions, "def models := 0\n").unwrap();
    let old = lean_dir.join("MyFixture/Extraction/FunsExternal.lean");
    std::fs::create_dir_all(old.parent().unwrap()).unwrap();
    std::fs::write(&old, "def edited := 1\n").unwrap();

    let (output, success) = run_backend(&crate_dir, &[]);
    assert!(success, "{output}");
    assert!(output.contains("differs from"), "{output}");
    assert_eq!(read(&assumptions), "def models := 0\n");
    assert_eq!(read(&old), SHIM);
}

#[test]
fn a_member_level_project_files_key_overrides_the_workspace_level_one() {
    let dir = tempfile::tempdir().unwrap();
    let bin = dir.path().join("bin");
    stub_pipeline_tools(&bin, &extraction_stub(false));
    let root = dir.path().join("ws");
    std::fs::create_dir_all(&root).unwrap();
    std::fs::write(
        root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"member\"]\n",
    )
    .unwrap();
    std::fs::write(
        root.join("hax.toml"),
        format!("project-files = false\n{}", path_entries(&bin)),
    )
    .unwrap();
    let member = root.join("member");
    common::write_crate(&member, "fixture");
    std::fs::write(member.join("hax.toml"), "project-files = true\n").unwrap();

    let (output, success) = run_backend(&member, &[]);
    assert!(success, "{output}");
    assert!(member.join("proofs/lean/lakefile.toml").is_file());
    assert!(member.join("proofs/lean/Fixture.lean").is_file());
}

#[test]
fn a_formatting_variant_of_the_shim_is_not_rescued_into_assumptions() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = setup(dir.path());
    write_executable(&dir.path().join("bin/aeneas"), &extraction_stub(true));
    let lean_dir = crate_dir.join("proofs/lean");
    // A shim written with different formatting (say, by another hax
    // version): moving it to `Assumptions/` would make the model import
    // itself, so it must be cleared and the model seeded from the template.
    let old = lean_dir.join("MyFixture/Extraction/FunsExternal.lean");
    std::fs::create_dir_all(old.parent().unwrap()).unwrap();
    std::fs::write(&old, "import MyFixture.Assumptions.FunsExternal\r\n").unwrap();

    let (output, success) = run_backend(&crate_dir, &[]);
    assert!(success, "{output}");
    assert!(!output.contains("moved"), "{output}");
    assert_eq!(
        read(&lean_dir.join("MyFixture/Assumptions/FunsExternal.lean")),
        "-- fill in the external functions\n"
    );
    assert_eq!(read(&old), SHIM);
}

#[test]
fn a_failed_clearing_of_the_extraction_directory_fails_the_run() {
    use std::os::unix::fs::PermissionsExt;

    let dir = tempfile::tempdir().unwrap();
    let crate_dir = setup(dir.path());
    let extraction = crate_dir.join("proofs/lean/MyFixture/Extraction");
    std::fs::create_dir_all(&extraction).unwrap();
    let stale = extraction.join("Stale.lean");
    std::fs::write(&stale, "def stale := 0\n").unwrap();
    // A read-only directory makes the removal of its entries fail.
    std::fs::set_permissions(&extraction, std::fs::Permissions::from_mode(0o555)).unwrap();

    let (output, success) = run_backend(&crate_dir, &[]);
    std::fs::set_permissions(&extraction, std::fs::Permissions::from_mode(0o755)).unwrap();
    // A partial clearing would silently feed the stale definitions into
    // the build, so the run must fail before aeneas runs.
    assert!(!success, "{output}");
    assert!(output.contains("failed to remove"), "{output}");
    assert!(stale.is_file());
}

#[test]
fn a_failed_package_file_write_fails_the_run() {
    use std::os::unix::fs::PermissionsExt;

    let dir = tempfile::tempdir().unwrap();
    let crate_dir = setup(dir.path());
    let lean_dir = crate_dir.join("proofs/lean");
    // The extraction and llbc directories stay writable, but `lean_dir`
    // itself does not accept new entries: every package file write fails.
    std::fs::create_dir_all(lean_dir.join("MyFixture/Extraction")).unwrap();
    std::fs::create_dir_all(lean_dir.join("llbc")).unwrap();
    std::fs::set_permissions(&lean_dir, std::fs::Permissions::from_mode(0o555)).unwrap();

    let (output, success) = run_backend(&crate_dir, &[]);
    std::fs::set_permissions(&lean_dir, std::fs::Permissions::from_mode(0o755)).unwrap();
    assert!(!success, "{output}");
    assert!(output.contains("failed to write"), "{output}");
}

#[test]
fn a_virtual_workspace_has_no_crate_name_to_derive_the_package_name_from() {
    let dir = tempfile::tempdir().unwrap();
    let bin = dir.path().join("bin");
    stub_pipeline_tools(&bin, &extraction_stub(false));
    let root = dir.path().join("ws");
    std::fs::create_dir_all(&root).unwrap();
    std::fs::write(
        root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"member\"]\n",
    )
    .unwrap();
    std::fs::write(root.join("hax.toml"), path_entries(&bin)).unwrap();
    common::write_crate(&root.join("member"), "fixture");

    let (output, success) = run_backend(&root, &[]);
    assert!(!success, "{output}");
    assert!(output.contains("no root package"), "{output}");
    assert!(output.contains("proof scenario"), "{output}");
    assert!(!root.join("charon-invoked").exists());
}

#[test]
fn a_package_name_colliding_with_a_module_root_aborts_before_the_tools_run() {
    let dir = tempfile::tempdir().unwrap();
    let crate_dir = dir.path().join("crate");
    common::write_crate(&crate_dir, "hax");
    let bin = dir.path().join("bin");
    stub_pipeline_tools(&bin, &extraction_stub(false));
    std::fs::write(crate_dir.join("hax.toml"), path_entries(&bin)).unwrap();

    let (output, success) = run_backend(&crate_dir, &[]);
    assert!(!success, "{output}");
    assert!(output.contains("module root"), "{output}");
    assert!(output.contains("proof scenario"), "{output}");
    assert!(!crate_dir.join("charon-invoked").exists());
}
