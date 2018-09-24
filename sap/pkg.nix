{ mkDerivation, base, profunctors, stdenv }:
mkDerivation {
  pname = "sap";
  version = "0.1";
  src = ./.;
  libraryHaskellDepends = [ base profunctors ];
  homepage = "https://github.com/k0001/sap";
  description = "Sums and products";
  license = stdenv.lib.licenses.asl20;
}
