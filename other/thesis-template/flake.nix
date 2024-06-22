{
  description = "Description for the project";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    denv = {
      url = "github:iliayar/env.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = inputs@{ flake-parts, denv, ... }:
    flake-parts.lib.mkFlake { inputs = denv.inputs; } {
      imports = [ denv.flakeModules.default ];
      systems =
        [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { config, self', inputs', pkgs, system, ... }: {
        denvs.default = {
          denv.packages = with pkgs; [ typst plantuml just poppler_utils ];
        };
      };
      flake = { };
    };
}
