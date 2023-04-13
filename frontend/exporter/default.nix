{craneLib, stdenv, makeWrapper, lib, rustc, gcc }:
let
  commonArgs = {
    version = "0.0.1";
    src = craneLib.cleanCargoSource ./.;
  };
  pname = "circus-rust-frontend";
  cargoArtifacts = craneLib.buildDepsOnly (commonArgs // {
    pname = "${pname}-deps";
  });
in
craneLib.buildPackage (commonArgs // {
  inherit cargoArtifacts pname;
})
# circus // {
#   passthru = circus.passthru or {} // {
#     wrapped = circus-engine: stdenv.mkDerivation {
#       name = "circus";
#       buildInputs = [ makeWrapper ];
#       phases = ["installPhase"];
#       installPhase = ''
#       mkdir -p $out/bin
#       makeWrapper ${circus}/bin/cargo-circus $out/bin/cargo-circus \
#         --prefix PATH : ${
#           lib.makeBinPath [
#             circus
#             circus-engine
#             rustc gcc
#           ]
#         }
#     '';
#       meta.mainProgram = "cargo-circus";
#     };
#   };
# }
