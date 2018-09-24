{ pkgs }:

# To be used as `packageSetConfig` for a Haskell pacakge set
# (tried with ghc861, nixpkgs 05659962cd8c04a9e8bf05b298b735f5747bf12c)
let
src_moto =
  builtins.fetchGit {
    url = "https://gitlab.com/k0001/moto";
    rev = "02c66de6b63651cdc18c9d37ad8bc83c96f51205";
 };

in
pkgs.lib.composeExtensions
  (import "${src_moto}/hs-overlay.nix" { inherit pkgs; })
  (self: super: {
    sap = super.callPackage ./sap/pkg.nix {};

    _shell = self.shellFor { packages = p: [ p.sap ]; };
  })
