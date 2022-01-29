{
  description = "Data Analysis";
  
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-21.05";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = import nixpkgs { inherit system; };
        in
          {
            devShell = pkgs.mkShell {
              buildInputs = with pkgs; [
                (haskell.packages.ghc8104.ghcWithPackages (hpkgs: with hpkgs; [
                  haskell-language-server
                  stack
                  cabal-install
                  zlib
                ]))
                zlib
              ];
            };
          }
      );
}

