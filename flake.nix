{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    fstar = {
      url = "github:fstarlang/fstar";
      inputs = {
        flake-utils.follows = "flake-utils";
      };
    };
    nixpkgs.follows = "fstar/nixpkgs";
    crane = {
      url = "github:ipetkov/crane";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-utils.follows = "flake-utils";
      };
    };
    rust-overlay.follows = "crane/rust-overlay";
  };

  outputs = {flake-utils, nixpkgs, rust-overlay, crane, fstar, ...}:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [rust-overlay.overlays.default];
        };
        fstar-pkgs = fstar.packages.${system};
        fstar-bin = fstar-pkgs.fstar;
        ocamlPackages = fstar-pkgs.ocamlPackages;
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
          thir-export =
            let
              commonArgs = {
                version = "0.0.1";
                src = craneLib.cleanCargoSource ./thir-export;
              };
              cargoArtifacts = craneLib.buildDepsOnly (commonArgs // {
                pname = "thir-export-deps";
              });
            in
              craneLib.buildPackage (commonArgs // {
                pname = "thir-export";
              });
          docs = nightly.rustc-docs;
          thir-elab = ocamlPackages.buildDunePackage {
            pname = "thir-elab";
            version = "0.0.1";
            duneVersion = "3";
            src = ./thir-elab;
            buildInputs = with ocamlPackages; [
              core base core_unix
              ppx_yojson_conv yojson ppx_sexp_conv ppx_hash
              visitors pprint non_empty_list bignum fstar-bin
              ppx_deriving_yojson ppx_matches ppx_let cmdliner
              angstrom
            ] ++ fstar-pkgs.fstar-dune.buildInputs;
            nativeBuildInputs = [ packages.thir-export pkgs.nodejs ];
            strictDeps = true;
            preBuild = "dune build thir-elab.opam";
          };
          circus = pkgs.symlinkJoin {
            name = "circus";
            paths = [
              packages.thir-elab
              packages.thir-export
              rustc
            ];
          };
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
        devShells = rec {
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
              fstar-bin
            ];

            inputsFrom = [
              packages.thir-elab
              packages.thir-export
            ];
          };
          circus = pkgs.mkShell {
            packages = [
              packages.circus
              pkgs.yq
            ];
          };
          default = circus;
        };
      }
    );
}
