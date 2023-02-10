{
  description = "TODO";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixos-22.05";
    rust-overlay = { 
      url = "github:oxalica/rust-overlay"; 
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, rust-overlay }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ rust-overlay.overlay ];
          };
        in
        {
          devShell = pkgs.mkShell rec {
            buildInputs = with pkgs; [
              rust-bin.stable.latest.default
              rust-analyzer
              rustfmt

              pkgconfig

              # Other packages
            ];
          };
        }
    );
}
