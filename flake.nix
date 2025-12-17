{
  description = "UVM Learning - Comparing UVM and Formal Verification with PicoRV32";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };
      in
      {
        devShells.default = pkgs.mkShell {
          name = "uvm-learning";

          buildInputs = with pkgs; [
            # ===================
            # Simulation Tools
            # ===================
            verilator              # High-performance Verilog simulator
            iverilog               # Icarus Verilog simulator
            gtkwave                # Waveform viewer

            # ===================
            # Formal Verification
            # ===================
            yosys                  # RTL synthesis framework
            sby                    # SymbiYosys formal verification frontend
            z3                     # SMT solver
            boolector              # SMT solver (good for bitvectors)
            yices                  # SMT solver

            # ===================
            # RISC-V Toolchain
            # ===================
            pkgsCross.riscv32.buildPackages.gcc   # RISC-V GCC cross-compiler
            pkgsCross.riscv32.buildPackages.binutils

            # ===================
            # Python Environment
            # ===================
            python3
            python3Packages.cocotb         # Python-based verification
            python3Packages.pytest
            python3Packages.pyyaml
            python3Packages.jinja2

            # ===================
            # Build Tools
            # ===================
            gnumake
            cmake
            pkg-config
            gcc
            gdb

            # ===================
            # Utilities
            # ===================
            git
            ripgrep
            fd
            jq
          ];

          shellHook = ''
            echo "=============================================="
            echo "  UVM Learning Development Environment"
            echo "  Target: PicoRV32 RISC-V Core"
            echo "=============================================="
            echo ""
            echo "Available Tools:"
            echo "  Simulation:  verilator, iverilog, gtkwave"
            echo "  Formal:      yosys, symbiyosys, z3, boolector"
            echo "  RISC-V:      riscv32-unknown-elf-gcc"
            echo "  Python:      python3, cocotb, pytest"
            echo ""
            echo "Directory Structure:"
            echo "  design/picorv32/  - PicoRV32 RISC-V core"
            echo "  test/uvm/         - UVM testbench"
            echo "  test/formal/      - Formal verification"
            echo "=============================================="

            # Set up environment variables
            export PROJECT_ROOT="$(pwd)"
            export DESIGN_DIR="$PROJECT_ROOT/design/picorv32"
            export UVM_TEST_DIR="$PROJECT_ROOT/test/uvm"
            export FORMAL_TEST_DIR="$PROJECT_ROOT/test/formal"
          '';
        };

        # Package for CI/CD if needed
        packages.default = pkgs.stdenv.mkDerivation {
          pname = "uvm-learning";
          version = "0.1.0";
          src = ./.;
          
          buildInputs = with pkgs; [
            verilator
            yosys
            symbiyosys
          ];
          
          buildPhase = ''
            echo "Building UVM Learning project..."
          '';
          
          installPhase = ''
            mkdir -p $out
            cp -r . $out/
          '';
        };
      }
    );
}
