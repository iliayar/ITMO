{
  description = "TODO";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/17b62c338f2a0862a58bb6951556beecd98ccda9";
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
              openssl

              # Other packages
            ];
          };
        }
    );
}
