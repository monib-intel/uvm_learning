// PicoRV32 UVM Testbench Package
//
// A SystemVerilog Package organizes related code into a namespace and
// controls compilation order. For UVM testbenches, the package includes
// all class definitions in the correct dependency order.
//
// PACKAGE STRUCTURE:
// ┌─────────────────────────────────────────────────────────────┐
// │                    picorv32_pkg                             │
// ├─────────────────────────────────────────────────────────────┤
// │  1. Import UVM library                                      │
// │     - import uvm_pkg::*                                     │
// │     - `include "uvm_macros.svh"                            │
// │                                                             │
// │  2. Transaction Classes (must come first)                   │
// │     - picorv32_mem_txn                                      │
// │                                                             │
// │  3. Agent Components (in dependency order)                  │
// │     - monitor (standalone)                                  │
// │     - driver (standalone)                                   │
// │     - sequencer (standalone)                                │
// │     - agent (uses above three)                              │
// │                                                             │
// │  4. Environment Components                                  │
// │     - scoreboard (uses transactions)                        │
// │     - coverage (uses transactions)                          │
// │     - env (uses agents, scoreboard, coverage)               │
// │                                                             │
// │  5. Tests                                                   │
// │     - tests (uses env)                                      │
// └─────────────────────────────────────────────────────────────┘
//
// KEY CONCEPTS:
//
// 1. COMPILATION ORDER MATTERS
//    - Base classes before derived classes
//    - Used classes before users
//    - Transactions before components that use them
//
// 2. UVM IMPORTS
//    - import uvm_pkg::* brings in all UVM base classes
//    - uvm_macros.svh provides `uvm_* macros
//
// 3. INCLUDE PATHS
//    - `include uses relative paths from package file location
//    - Alternative: use +incdir+ compile options
//
// 4. NAMESPACE ISOLATION
//    - Package contents accessed via import or package::item
//    - Prevents name collisions between projects
//
// USAGE:
//   // In tb_top or other modules:
//   import picorv32_pkg::*;  // Import all package contents
//
//============================================================================

package picorv32_pkg;
  
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  
  //==========================================================================
  // Transaction classes
  //==========================================================================
  `include "agents/picorv32_mem_txn.sv"
  
  //==========================================================================
  // Agent components
  //==========================================================================
  `include "agents/picorv32_mem_monitor.sv"
  `include "agents/picorv32_mem_driver.sv"
  `include "agents/picorv32_mem_sequencer.sv"
  `include "agents/picorv32_mem_agent.sv"
  
  //==========================================================================
  // Sequences (must come after sequencer, before environment)
  //==========================================================================
  `include "sequences/picorv32_sequences.sv"
  
  //==========================================================================
  // Environment components
  //==========================================================================
  `include "env/picorv32_virtual_sequencer.sv"
  `include "env/picorv32_scoreboard.sv"
  `include "env/picorv32_coverage.sv"
  `include "env/picorv32_env.sv"
  
  //==========================================================================
  // Virtual sequences (must come after virtual sequencer)
  //==========================================================================
  `include "sequences/picorv32_vseq.sv"
  
  //==========================================================================
  // Tests
  //==========================================================================
  `include "tests/picorv32_test.sv"
  
endpackage : picorv32_pkg
