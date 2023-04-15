{ocamlPackages, fetchzip, circus-rust-frontend, rustc, nodejs}:
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
in
ocamlPackages.buildDunePackage {
  pname = "circus-engine";
  version = "0.0.1";
  duneVersion = "3";
  src = ./.;
  buildInputs = with ocamlPackages; [
    core base core_unix
    ppx_yojson_conv yojson ppx_sexp_conv ppx_hash
    visitors pprint non_empty_list bignum
    ppx_deriving_yojson ppx_matches ppx_let cmdliner
    angstrom
  ] ++
  # F* dependencies
  [ batteries menhirLib ppx_deriving
    ppxlib sedlex stdint zarith ];
  nativeBuildInputs = [ rustc circus-rust-frontend nodejs ];
  strictDeps = true;
}
