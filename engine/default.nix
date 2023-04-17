{ocamlPackages, fetchzip, circus-rust-frontend, rustc, nodejs, closurecompiler, gnused, lib}:
let
  non_empty_list = 
    ocamlPackages.buildDunePackage rec {
      pname = "non_empty_list";
      version = "0.1";
      src = fetchzip {
        url = "https://github.com/johnyob/ocaml-non-empty-list/archive/refs/tags/${version}.zip";
        sha256 = "sha256-BJlEi0yG2DRT5vuU9ulucMD5MPFt9duWgcNO1YsigiA=";
      };
      buildInputs = with ocamlPackages; [ base ppxlib ppx_deriving ];
      duneVersion = "2";
      minimalOCamlVersion = "4.08";
      doCheck = false;
    };
  ppx_matches = 
    ocamlPackages.buildDunePackage rec {
      pname = "ppx_matches";
      version = "0.1";

      src = fetchzip {
        url = "https://github.com/wrbs/ppx_matches/archive/refs/tags/${version}.zip";
        sha256 = "sha256-nAmWF8MgW0odKkRiFcHGsvJyIxNHaZpnOlNPsef89Fo=";
      };

      buildInputs = [
        ocamlPackages.ppxlib
      ];
      duneVersion = "2";
      minimalOCamlVersion = "4.04";
      doCheck = false;
    };
  circus-engine = ocamlPackages.buildDunePackage {
    pname = "circus-engine";
    version = "0.0.1";
    duneVersion = "3";
    src = lib.sourceFilesBySuffices ./. [ ".ml" ".mli" ".js" "dune" "dune-project" ];
    buildInputs = with ocamlPackages; [
      zarith_stubs_js
      base
      ppx_yojson_conv yojson ppx_sexp_conv ppx_hash
      visitors pprint non_empty_list bignum
      ppx_deriving_yojson ppx_matches ppx_let cmdliner
      angstrom
    ] ++
    # F* dependencies
    [ batteries menhirLib ppx_deriving
      ppxlib sedlex stdint zarith ];
    nativeBuildInputs = [
      rustc circus-rust-frontend nodejs
      ocamlPackages.js_of_ocaml-compiler
    ];
    strictDeps = true;
    passthru = {
      js = circus-engine.overrideAttrs (old: {
        name = "circus-engine.js";
        nativeBuildInputs = old.nativeBuildInputs ++ [closurecompiler gnused];
        buildPhase = ''
          # Compile JS target
          dune build bin/js_driver.bc.js
          # Optimize the size of the JS file
          closure-compiler --js _build/default/bin/js_driver.bc.js --js_output_file circus-engine.js
          # Add a shebang & make executable
          sed -i '1 i #!/usr/bin/env node' circus-engine.js
          chmod +x circus-engine.js
        '';
        checkPhase = "true";
        installPhase = "cp circus-engine.js $out";
      });
    };
  };
in
circus-engine
