{ packages ? "coqPackages_8_7"

, rev      ? "d1ae60cbad7a49874310de91cd17708b042400c8"
, sha256   ? "0a1w4702jlycg2ab87m7n8frjjngf0cis40lyxm3vdwn7p4fxikz"

, pkgs     ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

with pkgs.${packages}; pkgs.stdenv.mkDerivation rec {
  name = "refine-freer";
  version = "1.0";

  src =
    if pkgs.lib.inNixShell
    then null
    else if pkgs ? coqFilterSource
         then pkgs.coqFilterSource [] ./.
         else ./.;

  buildInputs = [
    coq coq.ocaml coq.camlp5 coq.findlib
    equations fiat_HEAD coq-haskell
    (category-theory.overrideAttrs (attrs: rec {
       name = "coq${coq.coq-version}-category-theory-${version}";
       version = "20180709";
       src = pkgs.fetchFromGitHub {
         owner = "jwiegley";
         repo = "category-theory";
         rev = "3b9ba7b26a64d49a55e8b6ccea570a7f32c11ead";
         sha256 = "0f2nr8dgn1ab7hr7jrdmr1zla9g9h8216q4yf4wnff9qkln8sbbs";
         # date = 2018-03-26T17:10:21-07:00;
       };
       propagatedBuildInputs = [ coq ssreflect equations ];
     }))
  ];
  enableParallelBuilding = true;

  buildPhase = "make -j$NIX_BUILD_CORES";
  preBuild = "coq_makefile -f _CoqProject -o Makefile";
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
  passthru = {
    compatibleCoqVersions = v: builtins.elem v [ "8.6" "8.7" "8.8" ];
 };
}
