{
  description = "Development shell for prefix-trie and bit-permutation optimization";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { nixpkgs, flake-utils, rust-overlay, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ rust-overlay.overlays.default ];
        };

        # Miri requires nightly; select a nightly providing all requested components.
        rust = pkgs.rust-bin.selectLatestNightlyWith (toolchain:
          toolchain.default.override {
            extensions = [ "rust-src" "rustfmt" "clippy" "miri" ];
          });
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [
            rust
            pkgs.cargo-nextest
            pkgs.pkg-config
            pkgs.zstd
            pkgs.gnuplot
          ];

          # Use Nix's zstd for the Parquet benchmark dependency.
          ZSTD_SYS_USE_PKG_CONFIG = "1";
        };
      });
}
