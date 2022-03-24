args@{
  rev    ? "9222ae36b208d1c6b55d88e10aa68f969b5b5244"
, sha256 ? "0dvl990alr4bb64w9b32dhzacvchpsspj8p3zqcgk7q5akvqh1mw"
, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

let

metalib = coqPackages:
  with pkgs.${coqPackages}; pkgs.stdenv.mkDerivation rec {
    name = "coq${coq.coq-version}-metalib-${version}";
    version = "1.0";

    src = pkgs.fetchFromGitHub {
      owner = "plclub";
      repo = "metalib";
      rev = "be0f81cd12ee0e6e06863339cd3ee562dd94aaf9";
      sha256 = "sha256-Ranz5Dt4C5qN80oPZyMHovMlzjYJfA1sMUQ519ArSwo=";
      # date = 2017-09-17T22:08:18+10:00;
    };

    buildInputs = [
      coq coq.ocaml coq.camlp5 coq.findlib equations
    ];
    enableParallelBuilding = true;

    preBuild = ''
      cd Metalib
    '';

    buildFlags = [
      "JOBS=$(NIX_BUILD_CORES)"
    ];

    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

    env = pkgs.buildEnv { inherit name; paths = buildInputs; };
    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.14" "8.15" ];
    };
  };

equations-ln = coqPackages:
  with pkgs.${coqPackages}; pkgs.stdenv.mkDerivation rec {
    name = "coq${coq.coq-version}-equations-ln-${version}";
    version = "1.0";

    src = if pkgs ? coqFilterSource
          then pkgs.coqFilterSource [] ./.
          else ./.;

    buildInputs = [
      coq coq.ocaml coq.camlp5 coq.findlib equations (metalib coqPackages)
    ];
    enableParallelBuilding = true;

    preBuild = ''
      cd Stlc
      coq_makefile -f _CoqProject -o Makefile
    '';

    buildFlags = [
      "JOBS=$(NIX_BUILD_CORES)"
    ];

    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

    env = pkgs.buildEnv { inherit name; paths = buildInputs; };
    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.14" "8.15" ];
    };
  };

in {
  v8_14 = equations-ln "coqPackages_8_14";
  v8_15 = equations-ln "coqPackages_8_15";
}
