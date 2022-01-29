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
                (ghc.withPackages (hpkgs: with hpkgs; [
                  haskell-language-server
                  alex
                  happy
                ]))
              ];
            };
          }
      );
}

