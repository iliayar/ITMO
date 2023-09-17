{
  description = "DataBase Homework 1";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixos-23.05";
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = import nixpkgs {
            inherit system;
          };
        in
        {
          devShell = pkgs.mkShell rec {
            buildInputs = with pkgs; [
              postgresql_14

              (writeScriptBin "start_pg" ''
                pg_ctl start -l $LOG_PATH -o "-c listen_addresses= -c unix_socket_directories=$PGHOST"
              '')

              (writeScriptBin "stop_pg" ''
                pg_ctl stop
              '')
            ];


            shellHook = ''
              export PGDATA="$PWD/postgres_data";
              export PGHOST="$PWD/postgres";
              export LOG_PATH="$PWD/postgres/LOG";
              export PGDATABASE="postgres";
              export DATABASE_URL="postgresql://postgres?host=$PGHOST";
              
              if [ ! -d $PGHOST ]; then
                mkdir -p $PGHOST
              fi

              if [ ! -d $PGDATA ]; then
                echo "Initializing postgresql database..."
                initdb $PGDATA --auth=trust
              fi
            '';
          };
        }
    );
}
