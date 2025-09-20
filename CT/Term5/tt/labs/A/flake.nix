{
  description = "C Funciton Signatures Parser";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-21.05"; # Stable
    # nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in
          {
            devShell = pkgs.mkShell {
              buildInputs = with pkgs; [
                cargo
                rustc
                rustfmt
                rust-analyzer
                libiconv
              ];
            };
          }
      );
}
