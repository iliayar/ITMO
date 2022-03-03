{
  description = "Data Analysis";
  
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/554d2d8aa25b6e583575459c297ec23750adb6cb";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = import nixpkgs { inherit system; config = { allowUnfree = true; }; };
          pythonEnv = pkgs.python39.withPackages (pypkgs: with pypkgs; [
            # statsmodels
            jupyterlab
            # ipywidgets
            # numba
            # umap-learn
            # seaborn
            pandas
            # tqdm
            matplotlib
            numpy
            # scikit-learn
            # opencv4
            # pytorch-bin
            # torchvision-bin
            # pycuda
            # tensorflow-tensorboard
          ]);
        in
        {
            devShell = pkgs.mkShell {
              buildInputs = with pkgs; [
                pythonEnv
                nodePackages.pyright
                julia-bin
                ffmpeg
                # nodejs
                # cudatoolkit
              ];
            };
          }
      );
}

