# Continuous Integration (CI)

## Github Actions
 - [`add_to_project`](./.github/workflows/add_to_project.yml): each
   time an issue or a PR is open, this action adds it to the project
   [https://github.com/orgs/hacspec/projects/1](https://github.com/orgs/hacspec/projects/1).
 - [`release`](./.github/workflows/release.yml): whenever a tagged
   commit is pushed, this action builds the Linux binary, MacOS
   binary and JS of `hax-engine`, and uploads them to a new GitHub
   release.
 - [`format`](./.github/workflows/format.yml): ensure formatting for
   Rust and OCaml files.
 - [`specs`](./.github/workflows/specs.yml): compiles the toolchain
   (using Nix) and runs it on (for now) a selection of the examples
   provided by [hacspec/specs](https://github.com/hacspec/specs). For
   now this only tests the extraction of the specifications to Coq and
   FStar, we do not run Coq or FStar on the extractions.
 - [`test_installs`](./.github/workflows/test_installs.yml): compiles
   the toolchain on two versions of Ubuntu and two versions of MacOS
   using `apt` or `homebrew` and the `setup.sh` script.
 
## Merge queue
Additional actions are triggered on pull requests in the merge queue. They are
found in [`test_installs`](./.github/workflows/test_installs.yml).
