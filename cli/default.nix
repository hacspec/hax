{craneLib, stdenv, makeWrapper, lib, rustc, gcc, circus-engine, doCheck ? true }:
let
  pname = "circus";
  commonArgs = {
    version = "0.0.1";
    src = lib.cleanSourceWith {
      src = craneLib.path ./..;
      filter = path: type: builtins.isNull (builtins.match ".*/tests/.*" path) &&
                           (craneLib.filterCargoSources path type);
    };
    inherit doCheck;
  } // (if doCheck then {
    # [cargo test] builds independent workspaces. Each time another
    # workspace is added, it's corresponding lockfile should be added
    # in the [cargoLockList] list below.
    cargoVendorDir = craneLib.vendorMultipleCargoDeps {
      cargoLockList = [
        ../Cargo.lock
        ../tests/Cargo.lock
      ];
    };
  } else {});
  cargoArtifacts = craneLib.buildDepsOnly (commonArgs // {
    pname = pname;
  });
  circus = craneLib.buildPackage (commonArgs // {
    inherit cargoArtifacts pname;
  });
  binaries = [ circus circus-engine rustc gcc ];
  tests = craneLib.buildPackage (commonArgs // {
    inherit cargoArtifacts;
    pname = "circus-tests";
    doCheck = true;
    CI = "true";
    cargoBuildCommand = "true";
    cargoTestCommand = ''
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
  name = circus.name;
  buildInputs = [ makeWrapper ];
  phases = ["installPhase"];
  installPhase = ''
      mkdir -p $out/bin
      makeWrapper ${circus}/bin/cargo-circus $out/bin/cargo-circus \
        --prefix PATH : ${lib.makeBinPath binaries}
    '';
  meta.mainProgram = "cargo-circus";
  passthru = {
    unwrapped = circus;
    inherit tests;
  };
}
