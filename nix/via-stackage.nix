{ pkgs
, cleanedSource
, stackFile
, pkg-def-extras ? []
}:
let
  cleanedSource = pkgs.haskell-nix.cleanSourceHaskell { name = "czipwith-"+stackFile; src = ./..; };
  czipwith-nix = pkgs.haskell-nix.callStackToNix {
    name = "czipwith";
    src = cleanedSource;
    stackYaml = stackFile;
  };
  czipwith-plan = pkgs.haskell-nix.importAndFilterProject czipwith-nix;
  # czipwith-pkgs = {
  #   inherit (czipwith-plan.pkgs) modules resolver;
  #   extras = czipwith-plan.pkgs.extras ps;
  # };
  generatedCache = pkgs.haskell-nix.genStackCache {
    src = cleanedSource;
    stackYaml = stackFile;
  };
  hsPkgs = (pkgs.haskell-nix.mkStackPkgSet {
    stack-pkgs = czipwith-plan.pkgs;
    pkg-def-extras = pkg-def-extras;
    modules = pkgs.lib.singleton (pkgs.haskell-nix.mkCacheModule generatedCache);
  }).config.hsPkgs;
in {
  inherit czipwith-plan hsPkgs pkgs;
  inherit (hsPkgs) czipwith;
  inherit (hsPkgs.czipwith) checks;
  shell = hsPkgs.shellFor {
    # Include only the *local* packages of your project.
    packages = ps: with ps; [
      czipwith
    ];

    # Builds a Hoogle documentation index of all dependencies,
    # and provides a "hoogle" command to search the index.
    withHoogle = false;

    # You might want some extra tools in the shell (optional).

    # Some common tools can be added with the `tools` argument
    # tools = { cabal = "3.2.0.0"; };
    # See overlays/tools.nix for more details

    # Some you may need to get some other way.
    buildInputs = with pkgs.haskellPackages;
      [ cabal-install ghcid bash pkgs.nix ];

    # Prevents cabal from choosing alternate plans, so that
    # *all* dependencies are provided by Nix.
    exactDeps = true;
  };
}
# pkgs.haskell-nix.stackProject {
#   src = pkgs.haskell-nix.haskellLib.cleanGit { src = ./.; name = "czipwith"; };
#   pkg-def-extras = pkg-def-extras;
#   modules = [
#     { doHaddock = false; }
#   ];
# }
