{
  description = "Translation Methods Lab 1 on Perl";

  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          labDir = { term, subj, dir }: file: "/home/iliayar/Repos/ITMO/Term${toString term}/${subj}/${dir}/${file}";

          pkgs = nixpkgs.legacyPackages.${system};
          dir = labDir {
            term = 5;
            subj = "tm";
            dir  = "labs/lab1";
          };

          inputFile = dir "local.in"; 
          outputFile = dir "local.out";
          
          labRun = pkgs.writeShellScriptBin "labRun" ''
            perl $1 < local.in > local.out
          '';
        in
          {
            devShell = pkgs.mkShell {
              inherit inputFile outputFile;
              buildInputs = with pkgs; [
                labRun
                perl
              ];
            };
          }
      );
}
