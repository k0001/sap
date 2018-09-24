# This file exports every derivation introduced by this repository.
{ nixpkgs ? import ./nixpkgs.nix }:
let pkgs = import ./pkgs.nix { inherit nixpkgs; };
in
pkgs.releaseTools.aggregate {
  name = "everything";
  constituents = [
    pkgs._here.ghc861.sap
    pkgs._here.ghc861._shell
  ];
}

