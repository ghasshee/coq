
with import <nixpkgs> {};
stdenv.mkDerivation rec { 
    name = "Coq";
    src = null;
    buildInputs = with {}; 
    [
        coqPackages.ssreflect
        coq
        ];
}
