{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in with pkgs; {
        devShells.default = mkShell {
          packages = [
            stack
            ghcid
            (haskell-language-server.override {
              supportedGhcVersions = [ "92" ];
            })
          ];
        };
      }
    );
}
