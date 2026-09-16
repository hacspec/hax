//! The FLS suite: one test file per language construct under `fls/src/`, run
//! through each backend as a whole crate. The driver generates a cargo
//! package per test, observes how far the backend's pipeline gets, and
//! compares the observed stages with the results file committed for the
//! backend.

mod coverage;
mod exclusions;
mod ids;
mod lean;
mod package;
pub mod refresh;
mod results;
mod runner;
pub mod stage;
mod test;

use anyhow::{Result, bail};
use hax_types::cli_options::BackendName;

use self::{
    package::FlsContext, results::ResultsFile, runner::runner_for, stage::scale_of, test::FlsTest,
};
use crate::{
    cli::{Cli, FlsCommand},
    helpers::BackendNameExt,
    log::{BackendJobKind, JobKind},
};

/// Entry point of the `fls` subcommands.
pub async fn subcommand(options: &Cli, command: FlsCommand) -> Result<()> {
    match command {
        FlsCommand::Refresh { rev, check } => refresh::run(options, &rev, check),
        FlsCommand::Coverage => coverage::run(options).await,
    }
}

/// Entry point of the FLS suite.
pub async fn run(options: Cli) -> Result<()> {
    let ctx = FlsContext::new(options)?;
    let fls_dir = ctx.options.fls_dir();
    let tests = JobKind::ResolveTests
        .run(async |_| test::discover(&fls_dir))
        .await?;

    // Without `--backend`, the suite runs the Lean backend only until an
    // engine runner exists.
    let backends = ctx
        .options
        .backend()
        .map_or(vec![BackendName::Lean], |b| vec![b]);

    let mut failed = false;
    for backend in backends {
        // Every test with a tier for the backend has a table in the results
        // file; `--matching` narrows which of them are run.
        let with_tier: Vec<&FlsTest> = tests
            .iter()
            .filter(|test| test.tiers.contains_key(&backend))
            .collect();
        let selected: Vec<FlsTest> = with_tier
            .iter()
            .filter(|test| ctx.options.selects(&test.path))
            .cloned()
            .cloned()
            .collect();
        backend
            .job_kind(BackendJobKind::NumberBackendJobs(selected.len()))
            .report_no_message();
        let results_job = backend.job_kind(BackendJobKind::Phase {
            name: "results".into(),
        });

        let runner = runner_for(&ctx, backend)?;
        let tools = runner.tool_versions(&ctx).await?;
        let stages = runner.run(&ctx, &selected).await?;
        let checked = results_job
            .run(async |job| {
                if ctx.options.no_verify() {
                    job.report_message("results comparison skipped (--no-verify)");
                    return Ok(());
                }
                let file = ResultsFile::merged(
                    &ctx,
                    backend,
                    scale_of(backend)?,
                    tools.clone(),
                    &with_tier,
                    &selected,
                    &stages,
                )?;
                results::check(&ctx, &file, job).await
            })
            .await;
        match checked {
            Ok(()) => {}
            Err(e) if e.is::<results::ResultsDiffer>() => failed = true,
            Err(e) => return Err(e),
        }
    }
    if failed {
        bail!("observed results differ from the committed results files")
    }
    Ok(())
}
