{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
    name = "polyregular-shell";
    buildInputs = [ (import ./default.nix { inherit pkgs; }) ];
    # Ensure that libz.so and other libraries are available to TH
    # splices, cabal repl, etc.
    shellHook = ''
        export LD_LIBRARY_PATH+="${pkgs.zlib}/lib"
        export LC_ALL="C.UTF-8"
    '';
}
