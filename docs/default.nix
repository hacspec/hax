{ stdenv, buildPythonPackage, fetchPypi, setuptools, wheel, mkdocs
, mkdocs-material, }:
let
  mkdocs-glightbox = buildPythonPackage rec {
    pname = "mkdocs-glightbox";
    version = "0.4.0";

    src = fetchPypi {
      inherit pname version;
      hash = "sha256-OSs0IHv5WZEHGhbV+JFtHS8s1dW7Wa4pl0hczXeMcNk=";
    };

    doCheck = false;

    pyproject = true;
    build-system = with pkgs.python312Packages; [ setuptools wheel ];
  };

in stdenv.mkDerivation {
  name = "hax-docs";
  buildInputs = [ mkdocs mkdocs-material mkdocs-glightbox ];
  buildPhase = "mkdocs build";
  installPhase = "mv site $out"
}
