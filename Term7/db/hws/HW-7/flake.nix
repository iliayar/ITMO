{
  description = "Description for the project";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.05";
    denv = {
      url = "github:iliayar/env.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = inputs@{ flake-parts, denv, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ denv.flakeModules.default ];
      systems =
        [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { config, self', inputs', pkgs, system, ... }: {
        denvs.default = {
          services.postgres = {
            enable = true;
            defaultDatabase = "ctd";
          };

          scripts = {
            hw_run.text = ''
              echo "Reinit db..."
              psql <<EOF
              \c postgres;
              DROP DATABASE ctd;
              CREATE DATABASE ctd;
              EOF

              psql -f init.sql
              echo "Reinit task.."
              [ -e $1.sql ] && psql -f $1.sql || echo "No task $1"
              echo "Running tests..."
              [ -e $1_test.sql ] && psql -f $1_test.sql || echo "No test for task $1"
            '';
          };
        };
      };
      flake = { };
    };
}
