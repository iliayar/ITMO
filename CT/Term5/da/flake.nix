{
  description = "Data Analysis";
  
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    # nixpkgs.url = "github:NixOS/nixpkgs/nixos-21.05";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    # jupyterlab_vim_src = {
      # url = "github:jwkvam/jupyterlab-vim";
      # flake = false;
    # };
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = import nixpkgs { inherit system; config = { allowUnfree = true; }; };
          # jupyterlab_vim = pkgs.stdenv.mkDerivation {
            # name = "jupyterlab_vim";
            # src = jupyterlab_vim_src;
            # nativeBuildInputs = [
              # pkgs.python39Packages.jupyter-packaging
            # ];
            # installPhase = ''
              # mkdir -p $out/share/jupyter/lab/extensions
              # cp -r $src $out/share/jupyter/lab/extensions/jupyterlab_vim
            # '';
          # };
          pythonEnv = pkgs.python38.withPackages (pypkgs: with pypkgs; [
            statsmodels
            jupyterlab
            # jupyterlab_vim
            ipywidgets
            numba
            umap-learn
            seaborn
            pandas
            tqdm
            matplotlib
            numpy
            scikit-learn
            opencv4
            # (pytorch.override { cudaSupport = true; })
            pytorch-bin
            torchvision-bin
            pycuda
            tensorflow-tensorboard
          ]);
        in
        {
            devShell = pkgs.mkShell {
              buildInputs = with pkgs; [
                pythonEnv
                nodejs
                cudatoolkit
              ];
            };
          }
      );
}

