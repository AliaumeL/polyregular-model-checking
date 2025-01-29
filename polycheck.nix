{ pkgs ? import <nixpkgs> {} }:

let 
    hl = pkgs.haskell.lib;
    # use the package mona in ./mona.nx
    mona = (pkgs.callPackage ./mona.nix {});

    # build the haskell package in the ./polycheck/ directory
    # note that this automatically uses the `stack` build tool 
    # and dependencies, which is nice.
    # do not run tests and build docs!
    polycheck-pkg = pkgs.haskellPackages.developPackage {
        name = "polycheck-dev";
        root  = ./polycheck;
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

    # create a derivation that only exctracts the polycheck executable
    # created by polycheck-dev derivation 
    # and puts it in the /bin directory 
    polycheck = pkgs.stdenv.mkDerivation {
        name = "polycheck";
        buildInputs = [ polycheck-pkg ];
        src = polycheck-pkg.src;
        installPhase = ''
            mkdir -p $out/bin
            mkdir -p $out/assets
            cp ${polycheck-pkg}/bin/polycheck   $out/bin
            cp ${polycheck-pkg}/bin/benchmarker $out/bin
            cp -r ${./polycheck/assets}/* $out/assets/
        '';
    };

    polycheck-runtime = pkgs.buildEnv {
        name = "polycheck-runtime";
        paths = [ polycheck
                  mona
                  pkgs.cvc5
                  pkgs.z3
        ];
    };

    polycheck-devenv = pkgs.buildEnv {
        name = "polycheck-dev-env";
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

    # build the docker image for the polycheck project
    # it contains the polycheck executable,
    polycheck-img-small = pkgs.dockerTools.buildImage {
        name = "aliaume/polycheck-small";
        tag  = "latest";
        copyToRoot = pkgs.buildEnv { 
            name = "image-root-small";
            paths = [
                polycheck-runtime
                pkgs.fish
                pkgs.git 
                pkgs.deterministic-uname
                pkgs.coreutils
                (pkgs.runCommand "copy-assets" {} ''
                    mkdir -p $out/assets
                    cp -r ${./polycheck/assets}/* $out/assets/
                '')
            ];
            pathsToLink = ["/bin" "/assets" "/tmp"];
        };
        config = {
            Cmd = [ "${pkgs.fish}/bin/fish" ];
            WorkingDir = "/";
            ExposedPorts = {
                "3000/tcp" = {};
            };
        };
    };

    # a docker image with all the dev dependencies,
    # *without* the polycheck package
    polycheck-img-dev = pkgs.dockerTools.buildImage {
        name = "polycheck-docker-dev";
        tag  = "latest";
        copyToRoot = polycheck-devenv;
        config = {
            Cmd = [ "${pkgs.fish}/bin/fish" ];
            # workdir = /app 
            WorkingDir = "/app";
            extraCommands = ''
                mkdir -p $out/app/assets
                cp -r ${./polycheck/assets}/* $out/app/assets/
            '';
            exposedPorts = [ 3000 ];
        };
    };

in {
    polycheck         = polycheck;
    polycheck-runtime = polycheck-runtime;
    polycheck-img     = polycheck-img-small;
    polycheck-dev     = polycheck-img-dev;
    polycheck-devenv  = polycheck-devenv;
}
