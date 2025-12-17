// PicoRV32 Memory Interface
//
// A SystemVerilog Interface bundles related signals together and provides
// a clean abstraction between the DUT and testbench. Interfaces enable:
//   - Clean port connections (single connection vs. many wires)
//   - Clocking blocks for timing abstraction
//   - Modports for directional control
//   - Assertions and protocol checking
//
// PICORV32 MEMORY INTERFACE SIGNALS:
// ┌─────────────────────────────────────────────────────────────┐
// │                    PicoRV32 CPU                             │
// ├─────────────────────────────────────────────────────────────┤
// │  OUTPUTS (from CPU):                                        │
// │    mem_valid  - Request valid                               │
// │    mem_instr  - Instruction fetch (vs data access)          │
// │    mem_addr   - 32-bit address                              │
// │    mem_wdata  - Write data                                  │
// │    mem_wstrb  - Byte write strobes (0=read, non-0=write)    │
// │    trap       - CPU entered trap state                      │
// │                                                             │
// │  INPUTS (to CPU):                                           │
// │    mem_ready  - Memory response ready                       │
// │    mem_rdata  - Read data                                   │
// └─────────────────────────────────────────────────────────────┘
//
// KEY CONCEPTS:
//
// 1. CLOCKING BLOCKS
//    - Abstract timing from testbench code
//    - Specify input/output skew relative to clock
//    - Prevent race conditions between TB and DUT
//    - Example: @(driver_cb) waits for clocking block event
//
// 2. MODPORTS
//    - Define signal directions for different users
//    - driver modport: What driver sees (outputs to drive)
//    - monitor modport: What monitor sees (all inputs)
//    - dut modport: DUT's perspective
//
// 3. VIRTUAL INTERFACE
//    - Class-based testbench cannot directly access module signals
//    - Virtual interface = handle to actual interface instance
//    - Stored in uvm_config_db, retrieved by components
//
// USAGE PATTERN:
//   // In tb_top (module context):
//   picorv32_mem_if mem_if(clk, resetn);
//   uvm_config_db#(virtual picorv32_mem_if)::set(null, "*", "mem_vif", mem_if);
//
//   // In UVM component (class context):
//   virtual picorv32_mem_if vif;
//   uvm_config_db#(virtual picorv32_mem_if)::get(this, "", "mem_vif", vif);
//
//============================================================================

interface picorv32_mem_if(input logic clk, input logic resetn);
  
  // Memory interface signals
  logic        mem_valid;
  logic        mem_instr;
  logic        mem_ready;
  logic [31:0] mem_addr;
  logic [31:0] mem_wdata;
  logic [ 3:0] mem_wstrb;
  logic [31:0] mem_rdata;
  
  // Trap signal
  logic        trap;
  
  // Look-ahead interface (directly from DUT, optional monitoring)
  logic        mem_la_read;
  logic        mem_la_write;
  logic [31:0] mem_la_addr;
  logic [31:0] mem_la_wdata;
  logic [ 3:0] mem_la_wstrb;
  
  // Clocking blocks for driver and monitor
  clocking driver_cb @(posedge clk);
    default input #1step output #1step;
    input  mem_valid;
    input  mem_instr;
    output mem_ready;
    input  mem_addr;
    input  mem_wdata;
    input  mem_wstrb;
    output mem_rdata;
    input  trap;
  endclocking
  
  clocking monitor_cb @(posedge clk);
    default input #1step;
    input mem_valid;
    input mem_instr;
    input mem_ready;
    input mem_addr;
    input mem_wdata;
    input mem_wstrb;
    input mem_rdata;
    input trap;
  endclocking
  
  // Modports
  modport driver(clocking driver_cb, input clk, input resetn);
  modport monitor(clocking monitor_cb, input clk, input resetn);
  modport dut(
    output mem_valid,
    output mem_instr,
    input  mem_ready,
    output mem_addr,
    output mem_wdata,
    output mem_wstrb,
    input  mem_rdata,
    output trap
  );
  
endinterface : picorv32_mem_if
