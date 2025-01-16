{ pkgs ? import <nixpkgs> {} }:

let 
    hl = pkgs.haskell.lib;
    # use the package mona in ./mona.nx
    mona = (pkgs.callPackage ./mona.nix {});

    # build the haskell package in the ./polyreg/ directory
    # note that this automatically uses the `stack` build tool 
    # and dependencies, which is nice.
    # do not run tests and build docs!
    polyreg-pkg = pkgs.haskellPackages.developPackage {
        name = "polyreg-dev";
        root  = ./polyreg;
        modifier = drv: 
            hl.dontHaddock (
            hl.dontCheck (
            hl.disableLibraryProfiling (
            hl.disableExecutableProfiling (
            hl.enableStaticLibraries (
            hl.justStaticExecutables 
            (pkgs.haskell.lib.addBuildTools drv [
                mona
                pkgs.haskellPackages.stack
                pkgs.haskellPackages.BNFC
                pkgs.gmp
                pkgs.zlib
            ]))))));
    };

    # create a derivation that only exctracts the polyreg executable
    # created by polyreg-dev derivation 
    # and puts it in the /bin directory 
    polyreg-exe = pkgs.stdenv.mkDerivation {
        name = "polyreg-exe";
        buildInputs = [ polyreg-pkg ];
        src = polyreg-pkg.src;
        installPhase = ''
            mkdir -p $out/bin
            cp ${polyreg-pkg}/bin/polyreg-exe $out/bin
        '';
    };

    polyreg-runtime = pkgs.buildEnv {
        name = "polyreg-runtime";
        paths = [ polyreg-exe
                  mona
                  pkgs.cvc5
                  pkgs.z3
        ];
    };

    polyreg-devenv = pkgs.buildEnv {
        name = "polyreg-dev-env";
        paths = [ 
                  mona
                  pkgs.haskellPackages.stack
                  pkgs.haskellPackages.BNFC
                  pkgs.gmp
                  pkgs.zlib
                  pkgs.cvc5
                  pkgs.z3
                  pkgs.fish
        ];
    };

    # build the docker image for the polyreg project
    # it contains the polyreg executable,
    polyreg-img-small = pkgs.dockerTools.buildImage {
        name = "polyreg-docker-small";
        tag  = "latest";
        copyToRoot = pkgs.buildEnv { 
            name = "image-root-small";
            paths = [
                polyreg-runtime
                pkgs.fish
                pkgs.git
            ];
            pathsToLink = ["/bin"];
        };
        config = {
            Cmd = [ "${pkgs.fish}/bin/fish" ];
        };
    };

    # a docker image with all the dev dependencies,
    # *without* the polyreg package
    polyreg-img-dev = pkgs.dockerTools.buildImage {
        name = "polyreg-docker-dev";
        tag  = "latest";
        copyToRoot = polyreg-devenv;
        config = {
            Cmd = [ "${pkgs.fish}/bin/fish" ];
        };
    };

in {
    polyreg-exe     = polyreg-exe;
    polyreg-runtime = polyreg-runtime;
    polyreg-img     = polyreg-img-small;
    polyreg-dev     = polyreg-img-dev;
    polyreg-devenv  = polyreg-devenv;
}
