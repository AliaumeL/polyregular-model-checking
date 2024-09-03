{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
    name = "polyregular-shell";
    buildInputs = [ (import ./default.nix { inherit pkgs; }) ];
}
