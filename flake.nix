{
  description = "Description for the project";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = inputs@{ self, fenix, flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [
        # To import a flake module
        # 1. Add foo to inputs
        # 2. Add foo as a parameter to the outputs function
        # 3. Add here: foo.flakeModule

      ];
      systems =
        [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { config, self', inputs', pkgs, system, ... }:
        let
          rust = pkgs.fenix.complete.withComponents [
            "cargo"
            "clippy"
            "rust-src"
            "rustc"
            "rustfmt"
            "llvm-tools-preview"
          ];

          # Get the current git revision
          version = self.rev or self.dirtyRev;

          sdl_libs = with pkgs; [ SDL2 SDL2_image SDL2_mixer SDL2_ttf ];
        in {
          # Per-system attributes can be defined here. The self' and inputs'
          # module parameters provide easy access to attributes of the same
          # system.
          _module.args.pkgs = import inputs.nixpkgs {
            inherit system;
            overlays = [ fenix.overlays.default ];
            config = { };
          };

          # Equivalent to  inputs'.nixpkgs.legacyPackages.hello;
          packages.default = pkgs.rustPlatform.buildRustPackage {
            pname = "nes_emulator";
            inherit version;
            src = ./.;

            buildInputs = sdl_libs;

            cargoLock = { lockFile = ./Cargo.lock; };

            meta = with pkgs.lib; {
              description = "A nes emulator written in rust";
              homepage = "https://github.com/dreadster3/nes_emulator";
              license = licenses.unlicense;
              maintainers = [ maintainers.tailhook ];
            };
          };

          # Dev shells
          devShells.default = pkgs.mkShell {
            buildInputs = with pkgs; [ rust grcov ] ++ sdl_libs;
            LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath sdl_libs;
          };
        };
      flake = {
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

      };
    };
}

