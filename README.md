# UVM Learning

A comprehensive guide to learning and exploring the Universal Verification Methodology (UVM) for digital design verification using SystemVerilog.

## What is UVM?

Universal Verification Methodology (UVM) is a standardized, open-source methodology for verifying hardware designs. It provides a reusable base class library and best practices for building scalable, maintainable testbenches in SystemVerilog. UVM enables:

- **Reusability**: Testbench components can be reused across projects
- **Modularity**: Clear separation of concerns with layered architecture
- **Scalability**: Testbenches can grow from simple to highly complex verification environments
- **Productivity**: Reduces time-to-market by leveraging proven verification patterns
- **Standardization**: Industry-standard approach adopted by most major semiconductor companies

## UVM Architecture Overview

The UVM methodology is built on key components:

1. **Testbench Top**: The top-level module containing the design and verification components
2. **Environment (UVM_env)**: Container for all verification components
3. **Agent (UVM_agent)**: Contains driver, monitor, and sequencer for a specific interface
4. **Driver**: Translates high-level transactions into pin-level signals
5. **Monitor**: Observes pin-level signals and collects functional information
6. **Sequencer**: Controls stimulus generation through sequences
7. **Scoreboard**: Compares actual vs. expected behavior
8. **Functional Coverage**: Tracks which scenarios have been exercised

## Open-Source Simulator Options

Several open-source simulators support UVM testbench development:

### 1. **Verilator**
- High-performance C++ based simulator
- Excellent for combinational and synchronous logic
- Fast compilation and simulation
- Limited analog support
- Website: [verilator.org](https://www.verilator.org)

### 2. **Icarus Verilog (iverilog)**
- Free, open-source Verilog simulator
- Good for learning and educational purposes
- Limited SystemVerilog support
- Smaller design support
- Website: [iverilog.foshee.net](http://iverilog.foshee.net)

### 3. **GHDL**
- Open-source VHDL simulator
- Can be used alongside SystemVerilog simulators
- Good for mixed-language verification

### 4. **cocotb** (Constraint Object-oriented Testbench)
- Python-based hardware verification framework
- Language agnostic (works with any simulator via VPI/VHPI)
- Excellent for environments with Python expertise
- Integrates well with open-source simulators
- Website: [cocotb.org](https://www.cocotb.org)

### 5. **Commercial Simulators (with limited free options)**
- **QuestaSim**: Free version available (limited performance)
- **VCS**: Limited free academic version
- **Xcelium**: Professional version (paid, but industry standard)

## Contents

- Basic UVM examples
- Testbench templates
- Verification IP (VIP) examples
- Transaction-level modeling (TLM) examples
- Functional coverage examples

## Getting Started

### Prerequisites

- SystemVerilog knowledge (basic to intermediate)
- Understanding of hardware verification concepts
- A SystemVerilog simulator (see options above)
- UVM library (usually included with simulators or available from [opencores.org](https://opencores.org))

### Installation

1. Clone this repository
2. Install your chosen simulator
3. Set up UVM library paths in your environment
4. Run the example simulations

## Example Workflow

```bash
# Compile and simulate with open-source tools
verilator --cc design.v tb.sv -CFLAGS "-std=c++11"
make -C obj_dir -f Vdesign.mk

# Or with cocotb
pytest test_design.py
```

## Learning Resources

- **UVM Base Class Library**: IEEE Standard 1800.2
- **UVM Quick Reference**: Available at [UVM GitHub](https://github.com/accellera-official/uvm-core)
- **UVM Examples**: Official examples and tutorials

## Directory Structure

```
uvm_learning/
├── README.md
├── examples/
│   ├── basic_testbench/
│   ├── tlm_examples/
│   └── coverage_examples/
├── docs/
│   └── uvm_concepts.md
└── tools/
    └── scripts/
```

## Contributing

Feel free to fork this repository and add your own UVM examples and learning materials.

## License

This project is provided for educational purposes under the MIT License.
