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
    fstar-flake = {
      url = "github:FStarLang/FStar/v2023.09.03";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-utils.follows = "flake-utils";
      };
    };
    karamel = {
      url = "github:FStarLang/karamel";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        fstar.follows = "fstar-flake";
        flake-utils.follows = "flake-utils";
      };
    };
    hacl-star = {
      url = "github:hacl-star/hacl-star";
      flake = false;
    };
  };

  outputs = {
    flake-utils,
    nixpkgs,
    rust-overlay,
    crane,
    fstar-flake,
    hacl-star,
    karamel,
    ...
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [rust-overlay.overlays.default];
        };
        rustc = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;
        craneLib = (crane.mkLib pkgs).overrideToolchain rustc;
        ocamlformat = pkgs.ocamlformat_0_24_1;
        rustfmt = pkgs.rustfmt;
        fstar = fstar-flake.packages.${system}.default;
        krml = karamel.packages.${system}.default;
      in rec {
        packages = {
          inherit rustc ocamlformat rustfmt fstar krml;
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

          check-toolchain = checks.toolchain;
          check-examples = checks.examples;
        };
        checks = {
          toolchain = packages.hax.tests;
          examples = pkgs.callPackage ./examples {
            inherit (packages) hax;
            inherit craneLib fstar hacl-star;
          };
        };
        apps = {
          serve-rustc-docs = {
            type = "app";
            program = "${pkgs.writeScript "serve-rustc-docs" ''
              cd ${packages.rustc.passthru.availableComponents.rustc-docs}/share/doc/rust/html/rustc
              ${pkgs.python3}/bin/python -m http.server
            ''}";
          };
        };
        devShells = let
          inputsFrom = [
            packages.hax-rust-frontend.unwrapped
            packages.hax-engine
          ];
        in let
          packages = [
            ocamlformat
            pkgs.ocamlPackages.ocaml-lsp
            pkgs.ocamlPackages.ocamlformat-rpc-lib
            pkgs.ocamlPackages.ocaml-print-intf
            pkgs.ocamlPackages.odoc
            pkgs.ocamlPackages.utop

            pkgs.cargo-expand
            pkgs.cargo-insta
            pkgs.openssl.dev
            pkgs.pkg-config
            pkgs.rust-analyzer
            rustfmt
            rustc

            krml

            (pkgs.stdenv.mkDerivation {
              name = "rebuild-script";
              phases = ["installPhase"];
              installPhase = ''
                mkdir -p $out/bin
                cp ${./.utils/rebuild.sh} $out/bin/rebuild
              '';
            })
          ];
          LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";
        in {
          fstar-examples = pkgs.mkShell {
            inherit inputsFrom LIBCLANG_PATH;
            HACL_HOME = "${hacl-star}";
            packages = packages ++ [fstar krml];
          };
          default = pkgs.mkShell {
            KRMLLIB = "${krml}/lib/krml";
            inherit packages inputsFrom LIBCLANG_PATH;
          };
        };
      }
    );
}
