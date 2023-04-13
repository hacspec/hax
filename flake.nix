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
      in rec {
        packages = {
          inherit rustc;
          docs = rustc.rustc-docs;
          circus-engine = pkgs.callPackage ./engine {
            circus-rust-frontend = packages.circus-rust-frontend.unwrapped;
          };
          circus-rust-frontend = pkgs.callPackage ./cli {
            inherit rustc craneLib;
            inherit (packages) circus-engine;
          };
          circus = packages.circus-rust-frontend;
          default = packages.circus;
        };
        devShells = {
          default = pkgs.mkShell {
            inputsFrom = [
              packages.circus-rust-frontend.unwrapped
              packages.circus-engine
            ];
            packages = [
              pkgs.ocamlformat
              pkgs.ocamlPackages.ocaml-lsp
              pkgs.ocamlPackages.ocamlformat-rpc-lib
              pkgs.ocamlPackages.ocaml-print-intf

              pkgs.cargo-expand
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
