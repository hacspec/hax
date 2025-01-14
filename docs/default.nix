{ stdenv, buildPythonPackage, fetchPypi, setuptools, wheel, mkdocs
, mkdocs-material, fetchFromGitHub, natsort, wcmatch, hax-frontend-docs
, hax-engine-docs }:
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
    build-system = [ setuptools wheel ];
  };
  mkdocs-nav-weight = buildPythonPackage rec {
    pname = "mkdocs-nav-weight";
    version = "0.0.7";

    src = fetchPypi {
      inherit pname version;
      hash = "sha256-gAQGD3U3/NmWW/3uUSrCjo/T+rqdIlMkKn83TjDgbp0=";
    };

    doCheck = false;

    pyproject = true;
    build-system = [ setuptools wheel mkdocs ];
  };

in stdenv.mkDerivation {
  name = "hax-docs";
  src = ./..;
  buildInputs = [ mkdocs mkdocs-material mkdocs-glightbox mkdocs-nav-weight ];
  buildPhase = ''
    mkdocs build
  '';
  installPhase = ''
    mv site $out
    cp -rf ${hax-frontend-docs}/share/doc/ $out/frontend/docs
    cp -rf ${hax-engine-docs} $out/engine/docs
  '';
}
