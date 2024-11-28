{
  stdenv,
  lib,
  hax,
  coqPackages,
  gnused,
  craneLib,
}:
let
  commonArgs = {
    version = "0.1.0";
    src = craneLib.cleanCargoSource ../..;
    doCheck = false;
    cargoLockListrgoVendorDir = craneLib.vendorMultipleCargoDeps {
      cargoLockList = [
        ../Cargo.lock
        ../../Cargo.lock
      ];
    };
  };
  cargoArtifacts = craneLib.buildDepsOnly commonArgs;
in
  craneLib.mkCargoDerivation (commonArgs
    // {
      inherit cargoArtifacts;
      pname = "coverage";
      doCheck = false;
      buildPhaseCargoCommand = ''
        cp -r --no-preserve=mode ${../../proof-libs/coq/coq/generated-core} generated-core

        cd generated-core
        
        coq_makefile -f _CoqProject -o Makefile
        make
        sudo make install

        cd ../examples/coverage

        cargo hax into coq
        cd proofs/coq/extraction
        
        sed 's/_impl_f_/_f_/' < Coverage_Test_instance.v > Coverage_Test_instance.v # TODO: this is a hotfix, should be solved in backend and removed from here.
        coq_makefile -f _CoqProject -o Makefile
        make
      '';
      buildInputs = [
            hax
            coqPackages.coq-record-update
            coqPackages.coq
            gnused
      ];
    })
