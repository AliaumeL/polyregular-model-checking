{   stdenv,
    fetchFromGitHub,
    gcc,
    gnumake,
    autoconf,
    automake,
    libtool,
    pkg-config,
    m4,
    flex,
    bison
}:
stdenv.mkDerivation {
    pname = "mona";
    version = "1.4-18";
    src = fetchFromGitHub {
        owner = "cs-au-dk";
        repo = "MONA";
        rev = "ec5139";
        sha256 = "fppVQc2xP+IRoMVv9qzqafzONCSueCiSoqgL++qE3Go=";
    };
    buildInputs = [
       gcc 
       gnumake 
       autoconf 
       automake 
       libtool 
       pkg-config 
       m4
       flex
       bison
    ];
    buildPhase = ''
        ./configure --prefix=$out
        make
    '';
    installPhase = ''
        make install
    '';
}
