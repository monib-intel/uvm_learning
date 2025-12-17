# cocotb Makefile for PicoRV32
# This Makefile is included by the main test/uvm/Makefile

# Defaults - can be overridden
SIM ?= icarus
TOPLEVEL_LANG ?= verilog

# Design sources
VERILOG_SOURCES = $(PWD)/../../design/picorv32/picorv32.v

# Top-level module
TOPLEVEL = picorv32

# Python test module
MODULE = test_picorv32

# Extra arguments for Verilator
ifeq ($(SIM),verilator)
    EXTRA_ARGS += --trace --trace-structs
    EXTRA_ARGS += -Wno-DECLFILENAME -Wno-GENUNNAMED -Wno-UNUSEDSIGNAL -Wno-BLKSEQ
endif

# Include cocotb's make rules
include $(shell cocotb-config --makefiles)/Makefile.sim
