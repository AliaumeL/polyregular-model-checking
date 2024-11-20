{ pkgs ? import <nixpkgs> {} }:
pkgs.buildEnv {
  name = "polyregular-model-checking";
  paths = [
    # haskell setup
    #pkgs.ghc
    #pkgs.haskellPackages.stack
    #pkgs.haskellPackages.haskell-language-server
    #pkgs.gmp
    # alt-ergo prover (non-free)
    # pkgs.alt-ergo
    # cvc5 prover
    pkgs.cvc5
    # z3 prover
    pkgs.z3
    # latex building environment
    # only light version 
    # pkgs.texlive.combined.scheme-small
    # pandoc 
    # pkgs.pandoc
    # python
    #pkgs.python3
    # pytest
    #pkgs.python3Packages.pytest
    # MONA
    (pkgs.callPackage ./mona.nix {})
    # tygiel
    # (pkgs.callPackage ./simplified_transducer/tygiel.nix {})
  ];
}

