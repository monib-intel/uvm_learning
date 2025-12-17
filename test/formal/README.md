# PicoRV32 Formal Verification

This directory contains formal verification infrastructure for the PicoRV32 RISC-V processor.

## Overview

Formal verification provides **mathematical proof** that design properties hold for **all possible inputs**, unlike simulation which only tests specific scenarios.

## Directory Structure

```
test/formal/
├── README.md                 # This file
├── Makefile                  # Build automation
├── formal_top.sv             # Formal verification top-level wrapper
├── picorv32.sby              # Main SymbiYosys configuration
├── picorv32_bmc.sby          # Bounded Model Checking configuration
├── picorv32_prove.sby        # Inductive proof configuration
├── picorv32_cover.sby        # Cover property configuration
└── properties/
    ├── picorv32_props.sv         # Core formal properties
    ├── picorv32_model_checking.sv # Model checking properties
    ├── picorv32_equiv.sv         # Equivalence checking module
    └── picorv32_assertions.sv    # Comprehensive SVA assertions
```

## Prerequisites

### Required Tools

1. **SymbiYosys (sby)** - Formal verification front-end
2. **Yosys** - Open-source synthesis tool with SystemVerilog support
3. **SMT Solver** - At least one of:
   - Boolector (recommended for hardware)
   - Z3
   - Yices2

### Installation

#### Ubuntu/Debian
```bash
sudo apt install yosys symbiyosys boolector z3
```

#### Nix
```bash
nix-shell -p yosys symbiyosys boolector z3
```

#### From Source
```bash
# Install Yosys
git clone https://github.com/YosysHQ/yosys
cd yosys && make && sudo make install

# Install SymbiYosys
git clone https://github.com/YosysHQ/SymbiYosys
cd SymbiYosys && sudo make install

# Install Boolector
git clone https://github.com/Boolector/boolector
cd boolector && ./contrib/setup-btor2tools.sh && ./contrib/setup-lingeling.sh
./configure.sh && cd build && make && sudo make install
```

## Quick Start

1. **Check tool availability:**
   ```bash
   make check-tools
   ```

2. **Run bounded model checking (fast bug finding):**
   ```bash
   make bmc
   ```

3. **Run inductive proof (prove properties):**
   ```bash
   make prove
   ```

4. **Run cover analysis (check reachability):**
   ```bash
   make cover
   ```

5. **Run all verification modes:**
   ```bash
   make all
   ```

## Verification Modes

### Bounded Model Checking (BMC)

BMC unrolls the design for N cycles and checks if any assertions can fail within that bound.

- **Purpose**: Find bugs quickly
- **Limitation**: Cannot prove absence of bugs
- **Config**: `picorv32_bmc.sby`

```bash
make bmc
```

### Inductive Proof

Uses k-induction to mathematically prove properties hold for ALL cycles.

- **Purpose**: Complete proofs
- **Limitation**: May require strengthening invariants
- **Config**: `picorv32_prove.sby`

```bash
make prove
```

### Cover Analysis

Checks that interesting scenarios are reachable (not over-constrained).

- **Purpose**: Verify reachability
- **Limitation**: Only shows one trace per cover point
- **Config**: `picorv32_cover.sby`

```bash
make cover
```

## Property Categories

### Safety Properties
"Bad things never happen"
- PC word-alignment during instruction fetch
- Valid write strobe patterns
- No memory access during reset

### Protocol Properties
"Handshake compliance"
- Signals stable during transactions
- Proper request/acknowledge sequence

### Liveness Properties
"Good things eventually happen"
- Memory requests eventually complete
- Processor makes progress

### Cover Properties
"Interesting scenarios are reachable"
- Different store types occur
- Various PC values reached
- Trap conditions possible

## Interpreting Results

### PASS
```
[picorv32_bmc] PASS
```
Property holds within the verification bound.

### FAIL
```
[picorv32_bmc] FAIL
Counterexample trace written to picorv32_bmc/engine_0/trace.vcd
```
Property violated - examine the VCD file for the failing trace:
```bash
gtkwave picorv32_bmc/engine_0/trace.vcd
```

### UNKNOWN
```
[picorv32_prove] UNKNOWN
```
Solver couldn't determine result (timeout or complexity).

## Customization

### Adjusting Verification Depth

Edit the `.sby` file:
```
[options]
depth 100  # Increase for deeper exploration
```

### Adding New Properties

1. Create properties in `properties/your_props.sv`
2. Add to the `[files]` section in `.sby`
3. Instantiate in `formal_top.sv` if needed

### Changing Solver

Edit the `[engines]` section:
```
[engines]
smtbmc z3           # Use Z3 instead of Boolector
smtbmc --presat z3  # Use Z3 with preprocessing
```

## Debugging Tips

1. **Start with shallow depth** - Use `make quick` for fast feedback
2. **Check cover first** - Ensure interesting states are reachable
3. **Examine counterexamples** - VCD traces show exact failure path
4. **Add assumptions carefully** - Over-constraining hides bugs
5. **Strengthen invariants** - If induction fails, add helper properties

## References

- [SymbiYosys Documentation](https://symbiyosys.readthedocs.io/)
- [Yosys Manual](https://yosyshq.readthedocs.io/)
- [SVA Reference](https://www.systemverilog.io/sva)
- [PicoRV32 Formal Examples](../../design/picorv32/scripts/smtbmc/)
