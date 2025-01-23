# Engineering & Contributing Guidelines

The following is a set of guidelines for contributing to this repository.
These are mostly guidelines, not rules.
Use your best judgement, and feel free to propose changes to this document in a pull request.
The processes described here is not to pester you but to increase and maintain code quality.

## Working with this repository

We use issues to organise and prioritise work items.
If you start working on an issue, assign it to yourself so everyone knows it's being worked on.
Unassign yourself if you stop working on it and leave a comment why you stopped.

After picking up an issue create a branch.
There can be any number of branches and pull request for one issue.
But make sure that each issue is clearly linked to the pull request.
There must be one pull request that closes the issue.
If there are multiple PRs for an issue, make sure this is clear in the pull request.

## Pull Requests

We use the Github based PR workflow.
When starting to work on an issue create a branch and an according pull request that fixes the issue.
The changeset in a pull requests must not be larger than 1000 lines.
If an issue needs more work than that, split it into multiple pull requests.

After submitting the pull request, verify that all [status checks](https://help.github.com/articles/about-status-checks/) are passing before asking for review.

While the prerequisites above must be satisfied prior to having your pull request reviewed, the reviewer(s) may ask you to complete additional design work, tests, or other changes before your pull request can be ultimately accepted.

### PR & Commit Guidelines

- Split out mass-changes or mechanical changes into a separate PR from the substantive changes.
- Separate commits into conceptually-separate pieces for review purposes (even if you then later collapse them into a single changeset to merge), if technically possible.
- Address all comments from previous reviews (either by fixing as requested, or explaining why you haven't) before requesting another review.
- If your request only relates to part of the changes, say so clearly.

### Force pushing

It is fine to force-push either (1) before asking for a review or (2) after PR approval, just before merging. Otherwise, in between two reviews, please do not force-push.

### Regressions

When a PR introduces a regression, a fix should be submitted in a
window of 2 days, otherwise the PR will be reverted.

## Rules for the OCaml code
 - Never use the OCaml standard library, always use [`base`](https://v3.ocaml.org/p/base/latest/doc/index.html), [`core`](https://v3.ocaml.org/p/core/latest/doc/index.html) or [`stdlib`](https://v3.ocaml.org/p/stdlib/latest/doc/index.html) instead.
 - Avoid non-total functions (e.g. all the `_exn` functions in `base`).
 - Try to avoid exceptions, if possible.
 - Never use `==`, which is the physical equality, and almost never what you want.

### Changelog
Our changelog format is based on https://keepachangelog.com/.
Please add an entry in a subsection (`Added`, `Changed`, `Deprecated`, `Removed`, `Fixed` -- see https://keepachangelog.com/en/1.0.0/#how) for each notable change.

Please prefix with `engine:`, `frontend:` or similar.

## Styleguides

### Git Commit Messages

- Use the present tense
- Use the imperative mood
- Limit the first line to 80 characters
- Don't end the first line of the commit message with a period
- Reference issues and pull requests liberally after the first line
- If the patch is of nontrivial size, point to the important comments in the non-first lines of the commit message.

### Styleguide

Use `rustfmt` for every Rust code and `ocamlformat` for every OCaml
code. From the command line, run `cargo fmt` in the root of hax and
`dune fmt` in `engine`.

### Documentation Styleguide

Use [rustdoc](https://doc.rust-lang.org/rustdoc/index.html) comments
on Rust files and functions. Use
[`odoc`](https://ocaml.github.io/odoc/) comments on OCaml files. It is
mandatory on public functions and encouraged on internal functions.


## Reviews

As a reviewer always keep in mind the following principles

- Reviewing code is more valuable than writing code as it results in higher overall project activity. If you find you can't write code any more due to prioritizing reviews over coding, let's talk.
- You should respond to a review request within one working day of getting it, either with a review, a deadline by which you promise to do the review, or a polite refusal. If you think a patch is lower priority than your other work communicate that.

### Review Guidelines

- Check that issue is assigned and linked.
- Commit title and message make sense and says what is being changed.
- Check that the PR applies cleanly on the target branch.
- Check new files for license and administrative issues.
- Check out code changes
  - Run automated tests
  - Manually verify changes if possible
- Code review
  - Does the change address the issue at hand?
  - Is the code well documented?
  - Do you understand the code changes?
    - If not, add a comment. The PR can't be accepted in this stage.
  - Is the public API changed?
    - Are the changes well documented for consumers?
    - Do the changes break backwards compatibility?
    - Is the new API sensible/needed?
  - Is the code maintainable after these changes?
  - Are there any security issues with these changes?
  - Are all code changes tested?
  - Do the changes effect performance?
  - Look at the interdiff for second and subsequent reviews.
- Ask if more information is needed to understand and judge the changes.
