{craneLib, stdenv, makeWrapper, lib, rustc, gcc, circus-engine, doCheck ? true }:
let
  pname = "circus";
  commonArgs = {
    version = "0.0.1";
    src = craneLib.cleanCargoSource ./..;
    inherit doCheck;
  } // (if doCheck then {
    # [cargo test] builds independent workspaces. Each time another
    # workspace is added, it's corresponding lockfile should be added
    # in the [cargoLockList] list below.
    cargoVendorDir = craneLib.vendorMultipleCargoDeps {
      cargoLockList = [
        ../Cargo.lock
        ../frontend/lint/hacspec_tests/Cargo.lock
        ../frontend/lint/rust_tests/Cargo.lock
      ];
    };
  } else {});
  cargoArtifacts = craneLib.buildDepsOnly (commonArgs // {
    pname = "${pname}-deps";
  });
  circus = craneLib.buildPackage (commonArgs // {
    inherit cargoArtifacts pname;
  });
in
stdenv.mkDerivation {
  name = "circus";
  buildInputs = [ makeWrapper ];
  phases = ["installPhase"];
  installPhase = ''
      mkdir -p $out/bin
      makeWrapper ${circus}/bin/cargo-circus $out/bin/cargo-circus \
        --prefix PATH : ${
          lib.makeBinPath [
            circus
            circus-engine
            rustc gcc
          ]
        }
    '';
  meta.mainProgram = "cargo-circus";
  passthru = {
    unwrapped = circus;
  };
}
