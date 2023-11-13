{
  craneLib,
  stdenv,
  lib,
  hax,
  fstar,
  hacl-star,
}: let
  commonArgs = {
    version = "0.0.1";
    src = lib.cleanSourceWith {
      src = craneLib.path ./..;
      filter = path: type:
        !builtins.isNull (builtins.match ".*(Makefile|.*[.](rs|toml|lock|diff))$" path)
        || ("directory" == type);
    };
    doCheck = false;
    cargoVendorDir = craneLib.vendorMultipleCargoDeps {
      cargoLockList = [
        ./Cargo.lock
        ../Cargo.lock
      ];
    };
  };
  cargoArtifacts = craneLib.buildDepsOnly commonArgs;
in
  craneLib.mkCargoDerivation (commonArgs
    // {
      inherit cargoArtifacts;
      pname = "hax-examples";
      doCheck = false;
      buildPhaseCargoCommand = ''
        cd examples
        export CACHE_DIR=$(mktemp -d)
        export HINT_DIR=$(mktemp -d)
        export SHELL=${stdenv.shell}
        make
      '';
      buildInputs = [hax fstar];
      HAX_LIBS_HOME = "${../proof-libs/fstar}";
      HACL_HOME = "${hacl-star}";
    })
