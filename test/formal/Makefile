# ============================================================================
# PicoRV32 Formal Verification Makefile
# ============================================================================
# This Makefile provides convenient targets for running formal verification
# on the PicoRV32 RISC-V processor using SymbiYosys.
#
# Usage:
#   make bmc       - Run bounded model checking (bug finding)
#   make prove     - Run inductive proof (property proving)
#   make cover     - Run cover property analysis (reachability)
#   make all       - Run all verification modes
#   make clean     - Remove generated files
#   make help      - Show available targets
#
# Prerequisites:
#   - SymbiYosys (sby)
#   - Yosys with SystemVerilog support
#   - At least one SMT solver (boolector, z3, yices2)
# ============================================================================

# Configuration
SBY ?= sby
YOSYS ?= yosys

# Source files
DESIGN_DIR = ../../design/picorv32
PROP_DIR = properties

# Output directories
BMC_DIR = picorv32_bmc
PROVE_DIR = picorv32_prove
COVER_DIR = picorv32_cover

# Default target
.PHONY: all
all: bmc prove cover
	@echo "============================================"
	@echo "All formal verification tasks completed!"
	@echo "============================================"

# Bounded Model Checking (Bug Finding)
.PHONY: bmc
bmc:
	@echo "============================================"
	@echo "Running Bounded Model Checking..."
	@echo "============================================"
	$(SBY) -f picorv32_bmc.sby
	@echo "BMC completed. Check $(BMC_DIR)/ for results."

# Inductive Proof (Property Proving)
.PHONY: prove
prove:
	@echo "============================================"
	@echo "Running Inductive Proof..."
	@echo "============================================"
	$(SBY) -f picorv32_prove.sby
	@echo "Proof completed. Check $(PROVE_DIR)/ for results."

# Cover Property Analysis (Reachability)
.PHONY: cover
cover:
	@echo "============================================"
	@echo "Running Cover Property Analysis..."
	@echo "============================================"
	$(SBY) -f picorv32_cover.sby
	@echo "Cover analysis completed. Check $(COVER_DIR)/ for results."

# Quick BMC (shorter depth for fast feedback)
.PHONY: quick
quick:
	@echo "============================================"
	@echo "Running Quick BMC (depth=20)..."
	@echo "============================================"
	$(SBY) -f picorv32.sby --depth 20
	@echo "Quick check completed."

# Check tool availability
.PHONY: check-tools
check-tools:
	@echo "Checking for required tools..."
	@which $(SBY) > /dev/null || (echo "ERROR: SymbiYosys (sby) not found!" && exit 1)
	@which $(YOSYS) > /dev/null || (echo "ERROR: Yosys not found!" && exit 1)
	@which boolector > /dev/null || echo "WARNING: Boolector not found (optional)"
	@which z3 > /dev/null || echo "WARNING: Z3 not found (optional)"
	@echo "Tool check completed."

# View waveforms for failed properties
.PHONY: waves
waves:
	@echo "Opening waveform viewer..."
	@if [ -f $(BMC_DIR)/engine_0/trace.vcd ]; then \
		gtkwave $(BMC_DIR)/engine_0/trace.vcd; \
	elif [ -f $(PROVE_DIR)/engine_0/trace.vcd ]; then \
		gtkwave $(PROVE_DIR)/engine_0/trace.vcd; \
	else \
		echo "No trace files found. Run verification first."; \
	fi

# Clean generated files
.PHONY: clean
clean:
	@echo "Cleaning generated files..."
	rm -rf picorv32_bmc/
	rm -rf picorv32_prove/
	rm -rf picorv32_cover/
	rm -rf picorv32/
	rm -f *.log
	@echo "Clean completed."

# Help target
.PHONY: help
help:
	@echo "============================================"
	@echo "PicoRV32 Formal Verification Makefile"
	@echo "============================================"
	@echo ""
	@echo "Available targets:"
	@echo "  make all         - Run all verification modes"
	@echo "  make bmc         - Bounded model checking (find bugs)"
	@echo "  make prove       - Inductive proof (prove properties)"
	@echo "  make cover       - Cover analysis (check reachability)"
	@echo "  make quick       - Quick BMC with shallow depth"
	@echo "  make check-tools - Verify required tools are installed"
	@echo "  make waves       - Open waveform viewer for traces"
	@echo "  make clean       - Remove generated files"
	@echo "  make help        - Show this help message"
	@echo ""
	@echo "Configuration:"
	@echo "  SBY=$(SBY)"
	@echo "  YOSYS=$(YOSYS)"
	@echo ""
	@echo "Prerequisites:"
	@echo "  - SymbiYosys (sby)"
	@echo "  - Yosys with SystemVerilog support"
	@echo "  - SMT solver (boolector, z3, or yices2)"
