{
  description = "Description for the project";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
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
            langs.python = {
                enable = true;
                packages = pypkgs: with pypkgs; let
                    jupyter-mcp-tools = buildPythonPackage rec {
                        pname = "jupyter_mcp_tools";
                        version = "0.1.4";
                        format = "wheel";
                        src = pkgs.fetchPypi {
                            inherit pname version format;
                            dist = "py3";
                            python = "py3";
                            sha256 = "sha256-ZqYcph9sZT8JRuDcdwUbA32xq29iSjPoUaO3fl3KbCY=";
                        };
                    };
                in [
                    scikit-learn
                    pandas
                    numpy
                    matplotlib
                    keras
                    seaborn
                    ultralytics
                    speechrecognition
                    pocketsphinx

                    jupyter jupyterlab jupyter-collaboration jupyter-mcp-tools
                ];
            };
            denv.packages = with pkgs; [
                uv
            ];
            denv.env = {
                JUPYTER_URL = "http://localhost:8888";
                JUPYTER_TOKEN = "jupyter";
                ALLOW_IMG_OUTPUT = "true";
            };
        };
      };
      flake = { };
    };
}
