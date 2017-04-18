{ mkDerivation, base, profunctors, stdenv, tasty }:
mkDerivation {
  pname = "sums";
  version = "0.1";
  src = ./.;
  libraryHaskellDepends = [ base profunctors ];
  testHaskellDepends = [ base tasty ];
  homepage = "https://github.com/k0001/sums";
  description = "Open sum types";
  license = stdenv.lib.licenses.bsd3;
}
