{
  description = "Basic nodejs npm environment";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixos-22.05";
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = import nixpkgs {
            inherit system;
          };
          fixBinary = pkgs.writeShellScriptBin "fixBinary" ''
            patchelf \
            --set-interpreter "${pkgs.glibc}/lib/ld-linux-x86-64.so.2" \
            "$1"
          '';
        in
        {

          devShell = pkgs.mkShell rec {
            buildInputs = with pkgs; [
              nodePackages.npm
              nodePackages.typescript-language-server
              nodejs

              fixBinary
            ];
          };
        }
    );
}
