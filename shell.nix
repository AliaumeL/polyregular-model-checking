{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
    name = "polyregular-shell";
    buildInputs = [ (import ./default.nix { inherit pkgs; }) ];
    shellHook = ''
        export LC_ALL="C.UTF-8"
    '';
}
