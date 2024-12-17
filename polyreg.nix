{ pkgs ? import <nixpkgs> {} }:

let 
    hl = pkgs.haskell.lib;
    # use the package mona in ./mona.nx
    mona = (pkgs.callPackage ./mona.nix {});

    # build the haskell package in the ./polyreg/ directory
    # note that this automatically uses the `stack` build tool 
    # and dependencies, which is nice.
    # do not run tests and build docs!
    polyreg-dev = pkgs.haskellPackages.developPackage {
        name = "polycheck";
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
    polyreg = pkgs.stdenv.mkDerivation {
        name = "polyreg";
        buildInputs = [ polyreg-dev ];
        src = polyreg-dev.src;
        installPhase = ''
            mkdir -p $out/bin
            cp ${polyreg-dev}/bin/polyreg-exe $out/bin
        '';
    };

    polyreg-env = pkgs.buildEnv {
        name = "polyreg-env";
        paths = [ polyreg
                  mona
                  pkgs.cvc5
                  pkgs.z3
        ];
    };

    # build the docker image for the polyreg project
    # it contains the polyreg executable,
    polyregDocker = pkgs.dockerTools.buildImage {
        name = "polycheck-docker";
        tag  = "latest";
        copyToRoot = pkgs.buildEnv { 
            name = "image-root";
            paths = [
                polyreg-env
                pkgs.fish
            ];
            pathsToLink = ["/bin"];
        };
        config = {
            Cmd = [ "${pkgs.fish}/bin/fish" ];
            # create a volume for the "assets" directory
            Volumes = [ "/assets" ];
        };
    };

in {
    polyreg-exe = polyreg;
    polyreg-env = polyreg-env;
    polyreg-img = polyregDocker;
}