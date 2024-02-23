{
  description = "typst";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
  };

  outputs = { self, nixpkgs }: {

    packages.x86_64-linux.typst = nixpkgs.legacyPackages.x86_64-linux.typst;

    packages.x86_64-linux.default = self.packages.x86_64-linux.typst;

  };
}
