{
  ocamlPackages,
  fetchzip,
  hax-rust-frontend,
  hax-engine-names-extract,
  rustc,
  nodejs,
  jq,
  closurecompiler,
  gnused,
  lib,
  removeReferencesTo,
}: let
  non_empty_list = ocamlPackages.buildDunePackage rec {
    pname = "non_empty_list";
    version = "0.1";
    src = fetchzip {
      url = "https://github.com/johnyob/ocaml-non-empty-list/archive/refs/tags/${version}.zip";
      sha256 = "sha256-BJlEi0yG2DRT5vuU9ulucMD5MPFt9duWgcNO1YsigiA=";
    };
    buildInputs = with ocamlPackages; [base ppxlib ppx_deriving];
    duneVersion = "3";
    minimalOCamlVersion = "4.08";
    doCheck = false;
  };
  ppx_matches = ocamlPackages.buildDunePackage rec {
    pname = "ppx_matches";
    version = "0.1";

    src = fetchzip {
      url = "https://github.com/wrbs/ppx_matches/archive/refs/tags/${version}.zip";
      sha256 = "sha256-nAmWF8MgW0odKkRiFcHGsvJyIxNHaZpnOlNPsef89Fo=";
    };

    buildInputs = [
      ocamlPackages.ppxlib
    ];
    duneVersion = "3";
    minimalOCamlVersion = "4.04";
    doCheck = false;
  };
  hax-engine = ocamlPackages.buildDunePackage {
    pname = "hax-engine";
    version = "0.0.1";
    duneVersion = "3";
    src = lib.sourceFilesBySuffices ./. [".ml" ".mli" ".js" "dune" "dune-project" "sh" "rs" "mld"];
    buildInputs = with ocamlPackages;
      [
        zarith_stubs_js
        base
        ppx_yojson_conv
        yojson
        ppx_sexp_conv
        ppx_hash
        visitors
        pprint
        non_empty_list
        bignum
        ppx_deriving_yojson
        ppx_matches
        ppx_let
        ppx_enumerate
        cmdliner
        angstrom
        ppx_string
        logs
        core
        re
        js_of_ocaml
        ocamlgraph
      ]
      ++
      # F* dependencies
      [
        batteries
        menhirLib
        ppx_deriving
        ppxlib
        sedlex
        stdint
        zarith
      ];
    nativeBuildInputs = [
      rustc
      hax-rust-frontend
      hax-engine-names-extract
      nodejs
      ocamlPackages.js_of_ocaml-compiler
      jq
      removeReferencesTo
    ];
    strictDeps = true;
    installPhase = ''
      dune install --prefix=$bin --libdir=$lib/lib/ocaml/${ocamlPackages.ocaml.version}/site-lib/
      find "$bin" -type f -exec remove-references-to -t ${ocamlPackages.ocaml} '{}' +
    '';

    outputs = ["out" "bin" "lib"];
    passthru = {
      docs = hax-engine.overrideAttrs (old: {
        name = "hax-engine-docs";
        nativeBuildInputs =
          old.nativeBuildInputs
          ++ [
            ocamlPackages.odoc
          ];
        buildPhase = ''dune build @doc'';
        installPhase = "cp -rf _build/default/_doc/_html $out";
        outputs = ["out"];
      });
      js = hax-engine.overrideAttrs (old: {
        name = "hax-engine.js";
        nativeBuildInputs = old.nativeBuildInputs ++ [closurecompiler gnused];
        buildPhase = ''
          # Compile JS target
          dune build bin/js_driver.bc.js
          # Optimize the size of the JS file
          closure-compiler --js _build/default/bin/js_driver.bc.js --js_output_file hax-engine.js
          # Add a shebang & make executable
          sed -i '1 i #!/usr/bin/env node' hax-engine.js
          chmod +x hax-engine.js
        '';
        checkPhase = "true";
        installPhase = "cp hax-engine.js $out";
      });
    };
  };
in
  hax-engine
