{craneLib, stdenv, makeWrapper, lib, rustc, gcc, circus-engine }:
let
  pname = "circus";
  commonArgs = {
    version = "0.0.1";
    src = craneLib.cleanCargoSource ./..;
  };
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
