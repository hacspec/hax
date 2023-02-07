{
  inputs = {
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-utils.follows = "flake-utils";
      };
    };
    flake-utils.url = "github:numtide/flake-utils";
    crane.url = "github:ipetkov/crane";
    crane.inputs.nixpkgs.follows = "nixpkgs";
    fstar.url = "github:w95psp/fstar/record-payloads";
  };

  outputs = {flake-utils, nixpkgs, rust-overlay, crane, fstar, ...}:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [rust-overlay.overlays.default];
        };
        fstar-compiler-lib = (fstar.lib.${system}.binary-of-ml-snapshot {
          pname = "fstar";
          src = fstar;
          version = "compiler-lib";
          opts = {
            compileFStar = false;
            compileUlib = false;
            compileTests = false;
          };
        }).overrideAttrs (_: {
          patches = ./patch-fstar-lib.diff;
        });
        # fstar-bin = /home/lucas/repos/FStar/master/bin;
        # fstar-bin = fstar.packages.${system}.default.overrideAttrs (old: {
        #   patches = ./patch-fstar-lib.diff;
        # });
        ocamlPackages = pkgs.ocamlPackages;
        nightly = pkgs.rust-bin.nightly."2022-12-06";
        rustc = nightly.default.override {
          extensions = [
            "rustc-dev" "llvm-tools-preview"
            "rust-analysis"
            "rust-src"
          ];
        };
        craneLib = (crane.mkLib pkgs).overrideToolchain rustc;
        non_empty_list = 
          ocamlPackages.buildDunePackage rec {
            pname = "non_empty_list";
            version = "0.1";
            src = pkgs.fetchzip {
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

            src = pkgs.fetchzip {
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
      in rec {
        packages = {
          inherit rustc nightly;
          thir-export = craneLib.buildPackage {
            src = craneLib.cleanCargoSource ./thir-export;
          };
          docs = nightly.rustc-docs;
          thir-elab = ocamlPackages.buildDunePackage {
            pname = "thir-elab";
            version = "0.0.1";
            duneVersion = "3";
            src = ./thir-elab;
            buildInputs = with ocamlPackages; [
              base ppx_yojson_conv yojson ppx_sexp_conv ppx_hash
              visitors pprint non_empty_list bignum fstar-compiler-lib
              ppx_deriving_yojson ppx_matches
            ] ++ fstar-compiler-lib.buildInputs;
            nativeBuildInputs = [ packages.thir_ml_of_json_schema ];
            strictDeps = true;
            preBuild = "dune build thir-elab.opam";
          };
          thir_ml_of_json_schema = pkgs.writeScriptBin "thir_ml_of_json_schema" ''
            #!${pkgs.stdenv.shell}
            TEMP="$(mktemp -d)"
            trap 'rm -rf -- "$TEMP"' EXIT
            cd "$TEMP"
            echo 'profile = default' > .ocamlformat
            ${packages.thir-export}/bin/thir-export-json-schema - \
               | ${pkgs.nodejs}/bin/node ${./ocaml_of_json_schema.js} - - \
               | ${pkgs.ocamlformat}/bin/ocamlformat --impl -
          '';
        };
        apps = {
          serve-rustc-docs = { type = "app"; program = "${pkgs.writeScript "serve-rustc-docs" ''
             cd ${packages.docs}/share/doc/rust/html/rustc
             ${pkgs.python3}/bin/python -m http.server
          ''}"; };
          thir-json-visualizer = {
            type = "app";
            program = "${
              pkgs.writeScript "thir-json-visualizer"
                "${pkgs.nodejs}/bin/node '${./thir-json-visualizer/srv.js}' '${./thir-json-visualizer/build}'"
            }";
          };
          thir-export = {
            type = "app";
            program = "${
              pkgs.writeScript "thir-export"
                ''PATH="${packages.thir-export}/bin:${rustc}/bin/:$PATH" cargo thir-export "$@"''
            }";
          };
        };
        devShells = {
          thir-export = pkgs.mkShell {
            packages = [
              pkgs.cargo-expand
              pkgs.openssl.dev
              pkgs.pkg-config
              pkgs.rust-analyzer
              rustc
            ];
            LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";
          };
          thir-elab = pkgs.mkShell {
            packages = [
              pkgs.ocamlformat
              ocamlPackages.ocaml-lsp
              ocamlPackages.ocamlformat-rpc-lib
            ];

            inputsFrom = [
              packages.thir-elab
            ];
          };
        };
      }
    );
}
