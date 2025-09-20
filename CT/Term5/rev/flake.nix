{
  description = "Python angr";

  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in
          {
            devShell = pkgs.mkShell {
              buildInputs = with pkgs; [
                (python39.withPackages (pypkgs: with pypkgs; [
                  angr
                  z3
                ]))
              ];
            };
          }
      );
}
