{
  description = "Translation Methods Lab 1 on Perl";

  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          labDir = { term, subj, dir }: file: "/home/iliayar/Repos/ITMO/Term${toString term}/${subj}/${dir}/${file}";

          pkgs = nixpkgs.legacyPackages.${system};

          # Path settings
          dir = labDir {
            term = 5;
            subj = "tm";
            dir  = "labs/lab1";
          };

          # Input/Outputs files relative to lab directory
          inputFile = dir "local.in"; 
          outputFile = dir "local.out";
          
          # How to run
          labRun = pkgs.writeShellScriptBin "labRun" ''
            perl $1 < ${inputFile} > ${outputFile}
          '';

          # What packages you need
          needed = with pkgs; [
            perl
          ];
        in
          {
            devShell = pkgs.mkShell {
              inherit inputFile outputFile;
              buildInputs = needed;
            };
          }
      );
}

