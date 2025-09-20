{
  description = "Data Analysis";
  inputs = { flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/2b71ddd869ad592510553d09fe89c9709fa26b2b";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
      let
        pkgs = import nixpkgs { 
          inherit system; 
          config = { 
            allowUnfree = true;
            permittedInsecurePackages = [
              "julia-bin-1.0.5"
            ];
          }; 
        };
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
                qt5.qtbase
                qt5Full
                libGL

                pythonEnv
                nodePackages.pyright
                ffmpeg
                # nodejs
                # cudatoolkit
              ];
            };
          }
      );
}

