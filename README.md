# UVM Learning

A comprehensive guide comparing **UVM (Universal Verification Methodology)** and **Formal Verification** techniques for digital design verification. This project uses the open-source **PicoRV32** RISC-V core as a target design to demonstrate both verification approaches side-by-side.

## Project Goal

The primary objective of this repository is to:
1. **Compare UVM vs Formal Verification** - Understand the strengths and weaknesses of each approach
2. **Hands-on Learning** - Apply both methodologies to a real RISC-V processor design
3. **Best Practices** - Document when to use simulation-based vs. formal methods
4. **Hybrid Verification** - Explore how UVM and formal can complement each other

## Target Design: PicoRV32

**[PicoRV32](https://github.com/YosysHQ/picorv32)** is a size-optimized RISC-V CPU core implementing the RV32IMC instruction set. It's an ideal learning target because:
- Small and manageable (~2000 lines of Verilog)
- Created by the Yosys team with formal verification in mind
- Well-documented and actively maintained
- Includes built-in formal verification examples

---

## Table of Contents

### Part 1: UVM Design Fundamentals
1. [What is UVM?](#what-is-uvm)
2. [UVM Architecture Overview](#uvm-architecture-overview)
   - 2.1 Testbench Top
   - 2.2 Environment (UVM_env)
   - 2.3 Agent (UVM_agent)
   - 2.4 Driver, Monitor, Sequencer
   - 2.5 Scoreboard
   - 2.6 Functional Coverage
3. [UVM Phases](#uvm-phases)
   - 3.1 Build Phase
   - 3.2 Connect Phase
   - 3.3 Run Phase
   - 3.4 Extract/Check/Report Phases
4. [Transaction-Level Modeling (TLM)](#transaction-level-modeling-tlm)
   - 4.1 TLM Ports and Exports
   - 4.2 Analysis Ports
   - 4.3 FIFOs and Channels
5. [Sequences and Sequencers](#sequences-and-sequencers)
   - 5.1 Sequence Items
   - 5.2 Virtual Sequences
   - 5.3 Sequence Library
6. [Configuration and Factory](#configuration-and-factory)
   - 6.1 UVM Configuration Database
   - 6.2 Factory Overrides
   - 6.3 Parameterized Classes
7. [Functional Coverage in UVM](#functional-coverage-in-uvm)
   - 7.1 Covergroups and Coverpoints
   - 7.2 Cross Coverage
   - 7.3 Coverage-Driven Verification

### Part 2: Future of Formal Verification
8. [Introduction to Formal Verification](#introduction-to-formal-verification)
   - 8.1 What is Formal Verification?
   - 8.2 Formal vs. Simulation-Based Verification
   - 8.3 When to Use Formal Methods
9. [Formal Verification Techniques](#formal-verification-techniques)
   - 9.1 Model Checking
   - 9.2 Equivalence Checking
   - 9.3 Theorem Proving
   - 9.4 Property Checking (Assertions)
10. [SystemVerilog Assertions (SVA)](#systemverilog-assertions-sva)
    - 10.1 Immediate Assertions
    - 10.2 Concurrent Assertions
    - 10.3 Property Specification Language
11. [Emerging Trends in Formal Verification](#emerging-trends-in-formal-verification)
    - 11.1 AI/ML-Assisted Formal Verification
    - 11.2 Formal for Security Verification
    - 11.3 Formal in Safety-Critical Systems (ISO 26262, DO-254)
    - 11.4 Cloud-Based Formal Engines
12. [Hybrid Verification Approaches](#hybrid-verification-approaches)
    - 12.1 Formal + Simulation Integration
    - 12.2 Portable Stimulus Standard (PSS)
    - 12.3 Intelligent Testbench Automation
13. [Open-Source Formal Tools](#open-source-formal-tools)
    - 13.1 SymbiYosys
    - 13.2 Yosys + Boolector/Z3
    - 13.3 EBMC/CBMC
    - 13.4 NuSMV
14. [Commercial Formal Tools](#commercial-formal-tools)
    - 14.1 Cadence JasperGold
    - 14.2 Synopsys VC Formal
    - 14.3 Siemens Questa Formal
    - 14.4 OneSpin 360 DV

### Part 3: Practical Resources
14. [Open-Source Simulator Options](#open-source-simulator-options)
15. [Getting Started](#getting-started)
16. [Example Workflow](#example-workflow)
17. [Learning Resources](#learning-resources)
18. [Directory Structure](#directory-structure)
19. [Contributing](#contributing)
20. [License](#license)

---

## What is UVM?

Universal Verification Methodology (UVM) is a standardized, open-source methodology for verifying hardware designs. It provides a reusable base class library and best practices for building scalable, maintainable testbenches in SystemVerilog. UVM enables:

- **Reusability**: Testbench components can be reused across projects
- **Modularity**: Clear separation of concerns with layered architecture
- **Scalability**: Testbenches can grow from simple to highly complex verification environments
- **Productivity**: Reduces time-to-market by leveraging proven verification patterns
- **Standardization**: Industry-standard approach adopted by most major semiconductor companies

### Why UVM for PicoRV32?

When verifying a RISC-V processor like PicoRV32, UVM provides:

| Challenge | UVM Solution |
|-----------|--------------|
| Testing all RV32IMC instructions | Constrained random sequences generate diverse instruction mixes |
| Verifying memory interface timing | Agents with drivers/monitors check protocol compliance |
| Ensuring correctness | Scoreboards compare actual vs. expected execution results |
| Measuring completeness | Functional coverage tracks which instructions/scenarios tested |
| Reusing verification IP | Same memory agent works for any design with similar interface |

### UVM Class Hierarchy

```
uvm_object
├── uvm_transaction          <- Base for data items (e.g., RISC-V instruction)
├── uvm_sequence_item        <- Transaction with sequencer handshake
└── uvm_sequence             <- Generates streams of transactions

uvm_component
├── uvm_driver               <- Drives transactions to DUT pins
├── uvm_monitor              <- Observes DUT pins, creates transactions
├── uvm_sequencer            <- Routes sequences to driver
├── uvm_agent                <- Contains driver + monitor + sequencer
├── uvm_scoreboard           <- Checks expected vs. actual behavior
├── uvm_env                  <- Contains agents + scoreboard
└── uvm_test                 <- Top-level test configuration
```

### PicoRV32 UVM Testbench Concept

For PicoRV32, we'll build a UVM testbench with:

```
┌─────────────────────────────────────────────────────────────────┐
│                         UVM Test                                 │
├─────────────────────────────────────────────────────────────────┤
│                       UVM Environment                            │
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐  │
│  │  Memory Agent   │  │   IRQ Agent     │  │  PCPI Agent     │  │
│  │  ┌───────────┐  │  │  ┌───────────┐  │  │  ┌───────────┐  │  │
│  │  │  Driver   │  │  │  │  Driver   │  │  │  │  Driver   │  │  │
│  │  ├───────────┤  │  │  ├───────────┤  │  │  ├───────────┤  │  │
│  │  │  Monitor  │  │  │  │  Monitor  │  │  │  │  Monitor  │  │  │
│  │  ├───────────┤  │  │  ├───────────┤  │  │  ├───────────┤  │  │
│  │  │ Sequencer │  │  │  │ Sequencer │  │  │  │ Sequencer │  │  │
│  │  └───────────┘  │  │  └───────────┘  │  │  └───────────┘  │  │
│  └─────────────────┘  └─────────────────┘  └─────────────────┘  │
│                                                                  │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │                      Scoreboard                            │  │
│  │    Reference Model (ISS)  ←→  Actual PicoRV32 Output      │  │
│  └───────────────────────────────────────────────────────────┘  │
├─────────────────────────────────────────────────────────────────┤
│                     PicoRV32 DUT                                 │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐              │
│  │ Memory I/F  │  │   IRQ I/F   │  │  PCPI I/F   │              │
│  └─────────────┘  └─────────────┘  └─────────────┘              │
└─────────────────────────────────────────────────────────────────┘
```

---

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

### 2.1 Testbench Top

The testbench top is a SystemVerilog module that instantiates the DUT and connects it to the UVM environment through interfaces. It handles:
- Clock and reset generation
- Interface instantiation and connection to DUT
- UVM configuration database setup
- Test execution via `run_test()`

📄 **See implementation**: [`test/uvm/tb_top.sv`](test/uvm/tb_top.sv)

### 2.2 Environment (uvm_env)

The environment is the top-level container for all verification components. It creates and connects:
- Memory agent for CPU memory interface
- Scoreboard for result checking
- Coverage collector for functional coverage

📄 **See implementation**: [`test/uvm/env/picorv32_env.sv`](test/uvm/env/picorv32_env.sv)

### 2.3 Agent (uvm_agent)

An agent encapsulates the driver, monitor, and sequencer for a specific interface. Key features:
- Supports active (stimulus generation) and passive (monitoring only) modes
- Provides analysis port for broadcasting observed transactions
- Factory-enabled for easy customization

📄 **See implementation**: [`test/uvm/agents/picorv32_mem_agent.sv`](test/uvm/agents/picorv32_mem_agent.sv)

### 2.4 Driver, Monitor, Sequencer

| Component | Purpose | Implementation |
|-----------|---------|----------------|
| **Driver** | Converts transactions to pin-level activity, responds to CPU memory requests | [`picorv32_mem_driver.sv`](test/uvm/agents/picorv32_mem_driver.sv) |
| **Monitor** | Observes bus activity, creates transaction objects, broadcasts via analysis port | [`picorv32_mem_monitor.sv`](test/uvm/agents/picorv32_mem_monitor.sv) |
| **Sequencer** | Routes sequences to driver, controls stimulus flow | [`picorv32_mem_sequencer.sv`](test/uvm/agents/picorv32_mem_sequencer.sv) |
| **Transaction** | Data object representing a memory read/write | [`picorv32_mem_txn.sv`](test/uvm/agents/picorv32_mem_txn.sv) |

### 2.5 Scoreboard

The scoreboard compares actual DUT behavior against expected results:
- Tracks instruction fetches, data reads, and data writes
- Decodes RISC-V instructions for verification
- Reports errors and statistics at end of test

📄 **See implementation**: [`test/uvm/env/picorv32_scoreboard.sv`](test/uvm/env/picorv32_scoreboard.sv)

### 2.6 Functional Coverage

Functional coverage tracks which scenarios have been exercised:
- **Instruction opcode coverage**: All RV32IMC instruction types
- **Branch type coverage**: BEQ, BNE, BLT, BGE, etc.
- **Load/Store coverage**: LB, LH, LW, SB, SH, SW
- **Register usage coverage**: Which registers are used as rd, rs1, rs2
- **Address range coverage**: Memory regions accessed

📄 **See implementation**: [`test/uvm/env/picorv32_coverage.sv`](test/uvm/env/picorv32_coverage.sv)

---

## UVM Phases

UVM uses a phased execution model to ensure proper initialization, execution, and cleanup of testbench components. All components execute phases in a synchronized manner.

### 3.1 Build Phase

The **build phase** constructs the testbench hierarchy (top-down):
- Create child components using `type_id::create()`
- Retrieve configuration from `uvm_config_db`
- Pass configuration to children

### 3.2 Connect Phase

The **connect phase** establishes connections between components:
- Connect driver to sequencer via `seq_item_port`
- Connect monitor to scoreboard via analysis ports
- Set up virtual sequencer mappings

### 3.3 Run Phase

The **run phase** is where actual test execution occurs:
- Only phase that consumes simulation time
- Use objections (`raise_objection`/`drop_objection`) to control phase duration
- Start sequences on sequencers

### 3.4 Extract/Check/Report Phases

| Phase | Purpose |
|-------|---------|
| **Extract** | Collect final data from DUT/monitors |
| **Check** | Perform final correctness checks |
| **Report** | Print summary, coverage, pass/fail status |

### Complete Phase Execution Order

```
┌─────────────────────────────────────────────────────────────┐
│                    BUILD PHASES (top-down)                  │
├─────────────────────────────────────────────────────────────┤
│  build_phase        → Create components                     │
│  connect_phase      → Connect ports                         │
│  end_of_elaboration → Final topology adjustments            │
├─────────────────────────────────────────────────────────────┤
│                    RUN-TIME PHASES                          │
├─────────────────────────────────────────────────────────────┤
│  start_of_simulation → Print topology, initial checks       │
│  run_phase           → Main simulation (time-consuming)     │
│    ├── reset_phase                                          │
│    ├── configure_phase                                      │
│    ├── main_phase                                           │
│    └── shutdown_phase                                       │
├─────────────────────────────────────────────────────────────┤
│                    CLEANUP PHASES (bottom-up)               │
├─────────────────────────────────────────────────────────────┤
│  extract_phase      → Collect data                          │
│  check_phase        → Verify results                        │
│  report_phase       → Print final report                    │
│  final_phase        → Cleanup                               │
└─────────────────────────────────────────────────────────────┘
```

📄 **See test implementation**: [`test/uvm/tests/picorv32_test.sv`](test/uvm/tests/picorv32_test.sv)

---

## Transaction-Level Modeling (TLM)

TLM provides a standardized way for UVM components to communicate using transactions instead of signals. This abstraction improves reusability and simulation performance.

### 4.1 TLM Ports and Exports

TLM uses port-export pairs for communication:

| Component | Type | Purpose |
|-----------|------|---------|
| **Port** | `uvm_*_port` | Initiator - calls methods on connected export |
| **Export** | `uvm_*_export` | Target - implements the methods |
| **Imp** | `uvm_*_imp` | Implementation - terminal endpoint |

Common patterns:
- **Blocking**: `put()`, `get()` - waits for completion
- **Non-blocking**: `try_put()`, `try_get()` - returns immediately
- **Analysis**: `write()` - broadcast to multiple subscribers

### 4.2 Analysis Ports

Analysis ports implement publish-subscribe (one-to-many) communication:
- Monitor writes transactions to analysis port
- Multiple subscribers (scoreboard, coverage) receive copies
- Non-blocking - producer doesn't wait for consumers

### 4.3 FIFOs and Channels

TLM FIFOs buffer transactions between producer and consumer:
- `uvm_tlm_fifo`: Buffered channel with configurable depth
- `uvm_tlm_analysis_fifo`: Combines analysis export with FIFO

📄 **See TLM usage in**: [`test/uvm/env/picorv32_env.sv`](test/uvm/env/picorv32_env.sv)

---

## Sequences and Sequencers

Sequences generate stimulus by creating and sending transactions to drivers through sequencers.

### 5.1 Sequence Items

Sequence items (transactions) are the data objects that flow through the testbench:
- Extend `uvm_sequence_item`
- Define randomizable fields with constraints
- Include utility methods (convert2string, compare, copy)

📄 **See implementation**: [`test/uvm/agents/picorv32_mem_txn.sv`](test/uvm/agents/picorv32_mem_txn.sv)

### 5.2 Sequences

Sequences generate streams of transactions:
- Extend `uvm_sequence`
- Implement `body()` task to generate items
- Can call other sequences (hierarchical)

📄 **See implementation**: [`test/uvm/sequences/picorv32_sequences.sv`](test/uvm/sequences/picorv32_sequences.sv)

### 5.3 Virtual Sequences

Virtual sequences coordinate multiple sequencers:
- Don't generate items directly
- Start sub-sequences on different sequencers
- Enable complex multi-interface scenarios

📄 **See implementation**: [`test/uvm/sequences/picorv32_vseq.sv`](test/uvm/sequences/picorv32_vseq.sv)

---

## Configuration and Factory

UVM provides powerful mechanisms for runtime configuration and component customization.

### 6.1 UVM Configuration Database

`uvm_config_db` provides hierarchical configuration:
- Set values: `uvm_config_db#(type)::set(context, path, name, value)`
- Get values: `uvm_config_db#(type)::get(context, path, name, variable)`
- Wildcards in path enable broad configuration

### 6.2 Factory Overrides

The UVM factory enables runtime type substitution:
- **Type override**: Replace all instances of a type
- **Instance override**: Replace specific instance
- Enables test-specific component variations without code changes

### 6.3 Parameterized Classes

Parameterized components enable reuse across different configurations:
- Transaction types
- Interface widths
- Queue depths

📄 **See configuration usage in**: [`test/uvm/tests/picorv32_test.sv`](test/uvm/tests/picorv32_test.sv)

---

## Functional Coverage in UVM

Functional coverage measures verification completeness against the specification.

### 7.1 Covergroups and Coverpoints

Covergroups define what to measure:
- **Coverpoints**: Individual values/ranges to track
- **Bins**: Categories within a coverpoint
- **Sampling**: When to capture values

### 7.2 Cross Coverage

Cross coverage tracks combinations of coverpoints:
- Ensures all interesting combinations are tested
- Can use `ignore_bins` to exclude invalid combinations
- Critical for complex state machine verification

### 7.3 Coverage-Driven Verification

CDV methodology:
1. Create coverage model from specification
2. Run tests and collect coverage
3. Analyze coverage holes
4. Create directed tests for missing scenarios
5. Iterate until coverage goals met

📄 **See implementation**: [`test/uvm/env/picorv32_coverage.sv`](test/uvm/env/picorv32_coverage.sv)

---

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

- PicoRV32 RISC-V core (design under test)
- UVM testbench for PicoRV32
- Formal verification properties and proofs
- Comparison analysis and documentation
- Verification IP (VIP) examples
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
├── design/
│   └── picorv32/              # PicoRV32 RISC-V core (git submodule)
├── test/
│   ├── uvm/                   # UVM testbench environment
│   │   ├── env/               # UVM environment components
│   │   ├── agents/            # UVM agents (driver, monitor, sequencer)
│   │   ├── sequences/         # Test sequences
│   │   ├── tests/             # Test cases
│   │   └── tb_top.sv          # Testbench top
│   └── formal/                # Formal verification
│       ├── properties/        # SVA properties and assertions
│       ├── scripts/           # SymbiYosys scripts (.sby files)
│       └── proofs/            # Formal proof results
├── docs/
│   ├── uvm_concepts.md
│   └── formal_concepts.md
└── tools/
    └── scripts/
```

## Contributing

Feel free to fork this repository and add your own UVM examples and learning materials.

## License

This project is provided for educational purposes under the MIT License.
