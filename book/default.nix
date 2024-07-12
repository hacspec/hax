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
          '';
  installPhase = "mv book $out";
}
