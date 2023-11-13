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

              query=$(cat $1)
              query=$(echo $query  \
                | sd ":Mark" "0" \
                | sd ":LecturerId" "0" \
                | sd ":LecturerName" "'0'" \
                | sd ":StudentId" "0" \
                | sd ":StudentName" "'0'" \
                | sd ":CourseId" "0" \
                | sd ":CourseName" "'0'" \
                | sd ":GroupId" "0" \
                | sd ":GroupName" "'0'" \
                | sd ":FromGroupId" "0" \
                | sd ":FromGroupName" "'0'" \
              )
              explainQueryJson="EXPLAIN (FORMAT json, COSTS false, VERBOSE, ANALYZE) $query"
              explainQuery="EXPLAIN (COSTS false, VERBOSE, ANALYZE) $query"
              echo "Query: $query"

              echo "Without indexes:"
              psql <<EOF
              SET enable_seqscan=false;
              $explainQuery
              EOF
              echo "Create indexes.."
              psql -f index.sql
              psql <<EOF
              SET enable_seqscan=false;
              $explainQuery
              EOF

              echo "Indexes used: "
              (psql | rg '"Index Name"' | sd '.*"Index Name": "(.*)".*' '$1') <<EOF
              SET enable_seqscan=false;
              $explainQueryJson
              EOF
            '';
          };
        };
      };
      flake = { };
    };
}
