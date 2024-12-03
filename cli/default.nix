{
  craneLib,
  stdenv,
  makeWrapper,
  lib,
  rustc,
  gcc,
  hax-engine,
  doCheck ? true,
}: let
  pname = "hax";
  is-webapp-static-asset = path: builtins.match ".*(script[.]js|index[.]html)" path != null;
  commonArgs =
    {
      version = "0.0.1";
      src = lib.cleanSourceWith {
        src = craneLib.path ./..;
        filter = path: type:
          builtins.isNull (builtins.match ".*/tests/.*" path)
          && (craneLib.filterCargoSources path type || is-webapp-static-asset path);
      };
      inherit doCheck;
    }
    // (
      if doCheck
      then {
        # [cargo test] builds independent workspaces. Each time another
        # workspace is added, it's corresponding lockfile should be added
        # in the [cargoLockList] list below.
        cargoVendorDir = craneLib.vendorMultipleCargoDeps {
          cargoLockList = [
            ../Cargo.lock
            ../tests/Cargo.lock
          ];
        };
      }
      else {}
    );
  cargoArtifacts = craneLib.buildDepsOnly (commonArgs
    // {
      pname = pname;
    });
  hax = stdenv.mkDerivation {
    name = hax_with_artifacts.name;
    unpackPhase = "true";
    buildPhase = "true";
    installPhase = ''
      mkdir -p $out
      cp -r ${hax_with_artifacts}/bin $out/bin
    '';
  };
  hax_with_artifacts = craneLib.buildPackage (
    commonArgs
    // {
      inherit cargoArtifacts pname;
      doInstallCargoArtifacts = true;
    }
  );
  frontend-docs = craneLib.cargoDoc (commonArgs // {
    preBuildPhases = ["addRustcDocs"];
    cargoDocExtraArgs = "--document-private-items -p hax-bounded-integers";
    addRustcDocs = ''
      mkdir -p target/doc
      cp --no-preserve=mode -rf ${rustc.passthru.availableComponents.rustc-docs}/share/doc/rust/html/rustc/* target/doc/
    '';
    inherit cargoArtifacts pname;
  });
  docs = stdenv.mkDerivation {
    name = "hax-docs";
    unpackPhase = "true";
    buildPhase = "true";
    installPhase = ''
      mkdir $out
      cp -r ${frontend-docs}/share/doc $out/frontend
      cp -r ${hax-engine.docs}         $out/engine
      cd $out
      INDEX=$(mktemp)
      (
        echo "<style>"
        echo "body {font-family: Sans-Serif; margin: 0px; padding: 20px;}"
        echo "h1 {font-size: 140%;  font-weight: inherit;}"
        echo "</style>"
        echo "<h1>Hax docs</h1>"
        echo "<p>Hax is written both in Rust and OCaml. Documentation for each is available below:</p>"
        echo "<ul>"
        echo "<li><a href=\"frontend/hax_frontend_exporter/index.html\">Frontend documentation</a> (Rust)</li>"
        echo "<li><a href=\"engine/hax-engine/index.html\">Engine documentation</a> (OCaml)</li>"
        echo "</ul>"
      ) > $INDEX
      mv $INDEX index.html
    '';
  };
  binaries = [hax hax-engine.bin rustc gcc];
  tests = craneLib.buildPackage (commonArgs
    // {
      inherit cargoArtifacts;
      pname = "hax-tests";
      doCheck = true;
      CI = "true";
      cargoBuildCommand = "true";
      checkPhaseCargoCommand = ''
        SNAPS_DIR=test-harness/src/snapshots && rmdir "$SNAPS_DIR"
        TESTS_DIR=tests                      && rmdir "$TESTS_DIR"

        ln -s ${../test-harness/src/snapshots}        "$SNAPS_DIR"
        cp -r --no-preserve=mode   ${../tests}        "$TESTS_DIR"

        cargo test --test toolchain --profile release
      '';
      buildInputs = binaries;
      CARGO_TESTS_ASSUME_BUILT = "yes";
    });
in
  stdenv.mkDerivation {
    name = hax.name;
    buildInputs = [makeWrapper];
    phases = ["installPhase"];
    installPhase = ''
      mkdir -p $out/bin
      makeWrapper ${hax}/bin/cargo-hax $out/bin/cargo-hax \
        --prefix PATH : ${lib.makeBinPath binaries}
    '';
    meta.mainProgram = "cargo-hax";
    passthru = {
      unwrapped = hax;
      hax-engine-names-extract = craneLib.buildPackage (
        commonArgs
        // {
          pname = "hax_engine_names_extract";
          cargoLock = ../Cargo.lock;
          cargoToml = ../engine/names/extract/Cargo.toml;
          cargoArtifacts = hax_with_artifacts;
          nativeBuildInputs = [hax_with_artifacts];
          postUnpack = ''
            cd $sourceRoot/engine/names/extract
            sourceRoot="."
          '';
        }
      );
      engine-docs = hax-engine.docs;
      inherit tests docs frontend-docs;
    };
  }
