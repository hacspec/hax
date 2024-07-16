{
  stdenv,
  mdbook,
}:
stdenv.mkDerivation {
  name = "hax-book";
  src = ./.;
  buildInputs = [mdbook];
  buildPhase = ''
            mdbook build
            mdbook build archive -d ../book/archive
            bash ./postprocess.sh
          '';
  installPhase = "mv book $out";
}
