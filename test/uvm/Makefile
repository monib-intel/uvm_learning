# PicoRV32 UVM Testbench Makefile
# Supports multiple simulators

#==============================================================================
# Configuration
#==============================================================================
DESIGN_DIR = ../../design/picorv32
UVM_HOME ?= $(shell which vcs > /dev/null 2>&1 && echo "builtin" || echo "/opt/uvm-1.2")

# Design files
DESIGN_FILES = \
	$(DESIGN_DIR)/picorv32.v

# Testbench files
TB_FILES = \
	interfaces/picorv32_mem_if.sv \
	interfaces/picorv32_irq_if.sv \
	picorv32_pkg.sv \
	tb_top.sv

# Default test
TEST ?= picorv32_simple_test
FIRMWARE ?= firmware/simple_test.hex

# Simulation options
SEED ?= random
VERBOSITY ?= UVM_MEDIUM
TIMEOUT ?= 100000

#==============================================================================
# Verilator (limited UVM support - mainly for linting)
#==============================================================================
.PHONY: verilator-lint
verilator-lint:
	verilator --lint-only \
		-Wno-DECLFILENAME -Wno-GENUNNAMED -Wno-UNUSEDSIGNAL -Wno-BLKSEQ \
		-I$(DESIGN_DIR) \
		$(DESIGN_FILES) \
		--top-module picorv32

#==============================================================================
# Icarus Verilog (limited SystemVerilog/UVM support)
#==============================================================================
.PHONY: iverilog
iverilog:
	@echo "Note: Icarus Verilog has limited SystemVerilog/UVM support"
	iverilog -g2012 -Wall \
		-I$(DESIGN_DIR) \
		-DSIMULATION \
		$(DESIGN_FILES) \
		-o picorv32_tb.vvp

.PHONY: run-iverilog
run-iverilog: iverilog
	vvp picorv32_tb.vvp

#==============================================================================
# Synopsys VCS
#==============================================================================
VCS_OPTS = \
	-full64 -sverilog +v2k \
	-timescale=1ns/1ps \
	-ntb_opts uvm-1.2 \
	+incdir+$(DESIGN_DIR) \
	+incdir+. \
	+incdir+interfaces \
	+incdir+agents \
	+incdir+env \
	+incdir+sequences \
	+incdir+tests \
	+define+SIMULATION \
	-debug_access+all \
	-cm line+cond+fsm+tgl+branch \
	-cm_dir ./coverage

.PHONY: vcs
vcs:
	vcs $(VCS_OPTS) \
		$(DESIGN_FILES) \
		$(TB_FILES) \
		-o simv

.PHONY: run-vcs
run-vcs: vcs
	./simv +UVM_TESTNAME=$(TEST) \
		+UVM_VERBOSITY=$(VERBOSITY) \
		+firmware=$(FIRMWARE) \
		+ntb_random_seed=$(SEED) \
		-cm line+cond+fsm+tgl+branch \
		+dump

.PHONY: cov-vcs
cov-vcs:
	urg -dir coverage.vdb -report coverage_report

#==============================================================================
# Cadence Xcelium
#==============================================================================
XRUN_OPTS = \
	-64bit -sv \
	-timescale 1ns/1ps \
	-uvm \
	-uvmhome CDNS-1.2 \
	+incdir+$(DESIGN_DIR) \
	+incdir+. \
	+incdir+interfaces \
	+incdir+agents \
	+incdir+env \
	+incdir+sequences \
	+incdir+tests \
	+define+SIMULATION \
	-access +rwc \
	-coverage all

.PHONY: xrun
xrun:
	xrun $(XRUN_OPTS) \
		$(DESIGN_FILES) \
		$(TB_FILES) \
		+UVM_TESTNAME=$(TEST) \
		+UVM_VERBOSITY=$(VERBOSITY) \
		+firmware=$(FIRMWARE) \
		+dump

.PHONY: cov-xrun
cov-xrun:
	imc -load cov_work/scope -exec coverage_merge.tcl

#==============================================================================
# Mentor QuestaSim
#==============================================================================
VSIM_OPTS = \
	-64 -sv \
	+incdir+$(DESIGN_DIR) \
	+incdir+. \
	+incdir+interfaces \
	+incdir+agents \
	+incdir+env \
	+incdir+sequences \
	+incdir+tests \
	+define+SIMULATION

.PHONY: questa-compile
questa-compile:
	vlib work
	vlog $(VSIM_OPTS) $(DESIGN_FILES) $(TB_FILES)

.PHONY: questa
questa: questa-compile
	vsim -c -coverage tb_top \
		+UVM_TESTNAME=$(TEST) \
		+UVM_VERBOSITY=$(VERBOSITY) \
		+firmware=$(FIRMWARE) \
		-do "coverage save -onexit coverage.ucdb; run -all; quit"

.PHONY: cov-questa
cov-questa:
	vcover report -html coverage.ucdb

#==============================================================================
# Waveform Viewing
#==============================================================================
.PHONY: waves
waves:
	gtkwave picorv32_tb.vcd &

#==============================================================================
# Clean
#==============================================================================
.PHONY: clean
clean:
	rm -rf simv simv.daidir csrc *.vvp *.vcd *.log *.vpd
	rm -rf xcelium.d xrun.* *.shm
	rm -rf work transcript vsim.wlf
	rm -rf DVEfiles inter.vpd ucli.key
	rm -rf .simvision *.trn *.dsn
	rm -rf urgReport

#==============================================================================
# Help
#==============================================================================
.PHONY: help
help:
	@echo "PicoRV32 UVM Testbench"
	@echo "====================="
	@echo ""
	@echo "Targets:"
	@echo "  verilator-lint  - Lint design with Verilator"
	@echo "  vcs             - Compile with Synopsys VCS"
	@echo "  run-vcs         - Run simulation with VCS"
	@echo "  cov-vcs         - Generate VCS coverage report"
	@echo "  xrun            - Run with Cadence Xcelium"
	@echo "  cov-xrun        - Generate Xcelium coverage report"
	@echo "  questa          - Run with Mentor QuestaSim"
	@echo "  cov-questa      - Generate QuestaSim coverage report"
	@echo "  waves           - View waveforms with GTKWave"
	@echo "  clean           - Remove generated files"
	@echo ""
	@echo "Variables:"
	@echo "  TEST=<name>     - UVM test name (default: picorv32_simple_test)"
	@echo "  FIRMWARE=<file> - Firmware hex file (default: firmware/simple_test.hex)"
	@echo "  VERBOSITY=<lvl> - UVM verbosity (default: UVM_MEDIUM)"
	@echo "  SEED=<value>    - Random seed (default: random)"
	@echo ""
	@echo "Examples:"
	@echo "  make run-vcs TEST=picorv32_random_delay_test"
	@echo "  make xrun VERBOSITY=UVM_HIGH FIRMWARE=firmware/custom.hex"
	@echo "  make run-vcs && make cov-vcs"
