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
    fstar = {
      url = "github:FStarLang/FStar/v2024.01.13";
      inputs = {
        nixpkgs.follows = "nixpkgs";
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
    hacl-star,
    ...
  } @ inputs:
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
        fstar = inputs.fstar.packages.${system}.default;
        hax-env-file = pkgs.writeText "hax-env-file" ''
          HAX_PROOF_LIBS="${./proof-libs/fstar}"
          HAX_LIB="${./hax-lib}"
          HACL_HOME="${hacl-star}"
        '';
        hax-env = pkgs.writeScriptBin "hax-env" ''
          if [[ "$1" == "no-export" ]]; then
            cat "${hax-env-file}"
          else
            cat "${hax-env-file}" | xargs -I{} echo "export {}"
          fi
        '';
      in rec {
        packages = {
          inherit rustc ocamlformat rustfmt fstar hax-env;
          hax-engine = pkgs.callPackage ./engine {
            hax-rust-frontend = packages.hax-rust-frontend.unwrapped;
            hax-engine-names-extract = packages.hax-rust-frontend.hax-engine-names-extract;
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
          check-readme-coherency = checks.readme-coherency;
        };
        checks = {
          toolchain = packages.hax.tests;
          examples = pkgs.callPackage ./examples {
            inherit (packages) hax;
            inherit craneLib fstar hacl-star hax-env;
          };
          readme-coherency = let
            src = pkgs.lib.sourceFilesBySuffices ./. [".md"];
          in
            pkgs.stdenv.mkDerivation {
              name = "readme-coherency";
              inherit src;
              buildPhase = ''
                ${apps.replace-fstar-versions-md.program}
                diff -r . ${src}
              '';
              installPhase = "touch $out";
            };
        };
        apps = {
          replace-fstar-versions-md = {
            type = "app";
            program = "${pkgs.writeScript "replace-fstar-versions-md" ''
              FSTAR_VERSION=$(cat ${./flake.lock} | ${pkgs.jq}/bin/jq '.nodes.fstar.original.ref' -r)
              ${pkgs.fd}/bin/fd \
                 -X ${pkgs.sd}/bin/sd '`.*?`(<!---FSTAR_VERSION-->)' '`'"$FSTAR_VERSION"'`$1' **/*.md \
                 ";" --glob '*.md'
            ''}";
          };
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
            # `hax-engine`'s build requires `hax-rust-frontend` and
            # `hax-engine-names-extract`, but in a dev environment,
            # those two packages are supposed to be built locally,
            # thus we kill them here
            (packages.hax-engine.override {
              hax-rust-frontend = pkgs.hello;
              hax-engine-names-extract = pkgs.hello;
            })
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
          fstar = pkgs.mkShell {
            inherit inputsFrom LIBCLANG_PATH;
            shellHook = "eval $(hax-env)";
            packages = packages ++ [fstar hax-env];
          };
          default = pkgs.mkShell {
            inherit packages inputsFrom LIBCLANG_PATH;
          };
        };
      }
    );
}
