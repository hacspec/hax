{
  craneLib,
  stdenv,
  makeWrapper,
  lib,
  rustc,
  gcc,
}: let
  commonArgs = {
    version = "0.0.1";
    src = craneLib.cleanCargoSource ./.;
  };
  pname = "hax-rust-frontend";
  cargoArtifacts = craneLib.buildDepsOnly (commonArgs
    // {
      pname = "${pname}-deps";
    });
in
  craneLib.buildPackage (commonArgs
    // {
      inherit cargoArtifacts pname;
    })
# hax // {
#   passthru = hax.passthru or {} // {
#     wrapped = hax-engine: stdenv.mkDerivation {
#       name = "hax";
#       buildInputs = [ makeWrapper ];
#       phases = ["installPhase"];
#       installPhase = ''
#       mkdir -p $out/bin
#       makeWrapper ${hax}/bin/cargo-hax $out/bin/cargo-hax \
#         --prefix PATH : ${
#           lib.makeBinPath [
#             hax
#             hax-engine
#             rustc gcc
#           ]
#         }
#     '';
#       meta.mainProgram = "cargo-hax";
#     };
#   };
# }

