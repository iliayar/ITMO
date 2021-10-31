{
  description = "Data Analysis";
  
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    # nixpkgs.url = "github:NixOS/nixpkgs/nixos-21.05";
    nixpkgs.url = "nixpkgs/a5d03577f0161c8a6e713b928ca44d9b3feb2c37";
    jupyterlab_vim_src = {
      url = "github:jwkvam/jupyterlab-vim";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, jupyterlab_vim_src }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = import nixpkgs { inherit system; };
          jupyterlab_vim = pkgs.stdenv.mkDerivation {
            name = "jupyterlab_vim";
            src = jupyterlab_vim_src;
            nativeBuildInputs = [
              pkgs.python39Packages.jupyter-packaging
            ];
            installPhase = ''
              mkdir -p $out/share/jupyter/lab/extensions
              cp -r $src $out/share/jupyter/lab/extensions/jupyterlab_vim
            '';
          };
          pythonEnv = pkgs.python39.withPackages (pypkgs: with pypkgs; [
            statsmodels
            jupyterlab
            jupyterlab_vim
            seaborn
            pandas
            tqdm
            matplotlib
            numpy
            scikit-learn
          ]);
        in
        {
            devShell = pkgs.mkShell {
              buildInputs = with pkgs; [
                pythonEnv
                nodejs
              ];
            };
          }
      );
}

