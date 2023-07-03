{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    crane = {
      url = "github:ipetkov/crane";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-utils.follows = "flake-utils";
      };
    };
    rust-overlay.follows = "crane/rust-overlay";
  };

  outputs = {flake-utils, nixpkgs, rust-overlay, crane, ...}:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [rust-overlay.overlays.default];
        };
        rustc = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;
        craneLib = (crane.mkLib pkgs).overrideToolchain rustc;
        ocamlformat = pkgs.ocamlformat_0_24_1;
      in rec {
        packages = {
          inherit rustc ocamlformat;
          hax-engine = pkgs.callPackage ./engine {
            hax-rust-frontend = packages.hax-rust-frontend.unwrapped;
            inherit rustc;
          };
          hax-rust-frontend = pkgs.callPackage ./cli {
            inherit rustc craneLib;
            inherit (packages) hax-engine;
          };
          hax = packages.hax-rust-frontend;
          default = packages.hax;
        };
        checks.default = packages.hax.tests;
        apps = {
          serve-rustc-docs = { type = "app"; program = "${pkgs.writeScript "serve-rustc-docs" ''
             cd ${packages.rustc.passthru.availableComponents.rustc-docs}/share/doc/rust/html/rustc
             ${pkgs.python3}/bin/python -m http.server
          ''}"; };
        };
        devShells = {
          default = pkgs.mkShell {
            inputsFrom = [
              packages.hax-rust-frontend.unwrapped
              packages.hax-engine
            ];
            packages = [
              ocamlformat
              pkgs.ocamlPackages.ocaml-lsp
              pkgs.ocamlPackages.ocamlformat-rpc-lib
              pkgs.ocamlPackages.ocaml-print-intf
              pkgs.ocamlPackages.odoc
              pkgs.ocamlPackages.utop

              # pkgs.cargo-expand
              pkgs.openssl.dev
              pkgs.pkg-config
              pkgs.rust-analyzer
              rustc
            ];
            LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";
          };
        };
      }
    );
}
