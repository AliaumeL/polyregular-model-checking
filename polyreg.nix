{ pkgs ? import <nixpkgs> {} }:

let 
    # use the package mona in ./mona.nx
    mona = (pkgs.callPackage ./mona.nix {});

    # build the haskell package in the ./polyreg/ directory
    # note that this automatically uses the `stack` build tool 
    # and dependencies, which is nice.
    polyreg-dev = pkgs.haskellPackages.developPackage {
        name = "polycheck";
        root  = ./polyreg;
        modifier = drv: 
            pkgs.haskell.lib.addBuildTools drv [
                mona
                pkgs.haskellPackages.stack
                pkgs.haskellPackages.BNFC
                pkgs.gmp
                pkgs.zlib
            ];
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

    # build the docker image for the polyreg project
    # it contains the polyreg executable,
    # includes assets from the ./polyreg/assets directory as static files
    # and includes `mona`, `cvc5` and `z3` solvers
    polyregDocker = pkgs.dockerTools.buildImage {
        name = "polycheck-docker";
        tag  = "latest";
        copyToRoot = pkgs.buildEnv { 
            name = "image-root";
            paths = [
                polyreg
                mona
                pkgs.cvc5
                pkgs.z3
            ];
            pathsToLink = ["/bin"];
        };
    };

in {
    polyreg-exe = polyreg;
    polyreg-img = polyregDocker;
}
