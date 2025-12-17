// PicoRV32 UVM Testbench Top
//
// This is the top-level module that connects the DUT (Design Under Test) to
// the UVM verification environment. Key responsibilities:
//
// 1. CLOCK & RESET GENERATION
//    - Generates the system clock (100MHz = 10ns period)
//    - Implements reset sequence (active-low resetn)
//
// 2. INTERFACE INSTANTIATION
//    - Creates SystemVerilog interfaces that bundle related signals
//    - Interfaces provide a clean abstraction between DUT and testbench
//    - Clocking blocks in interfaces handle timing/synchronization
//
// 3. DUT INSTANTIATION
//    - Instantiates PicoRV32 with desired configuration parameters
//    - Connects DUT ports to interface signals
//
// 4. UVM CONFIGURATION
//    - Registers virtual interfaces in uvm_config_db
//    - This allows UVM components to access DUT signals
//    - Pattern: uvm_config_db#(type)::set(context, path, name, value)
//
// 5. TEST EXECUTION
//    - Calls run_test() to start the UVM test specified by +UVM_TESTNAME
//
// Usage:
//   vcs ... +UVM_TESTNAME=picorv32_simple_test +firmware=test.hex
//
//============================================================================

`timescale 1ns/1ps

module tb_top;
  
  import uvm_pkg::*;
  import picorv32_pkg::*;
  `include "uvm_macros.svh"
  
  //==========================================================================
  // Clock and Reset Generation
  //==========================================================================
  logic clk;
  logic resetn;
  
  // Clock generation (10ns period = 100MHz)
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end
  
  // Reset sequence
  initial begin
    resetn = 0;
    repeat(10) @(posedge clk);
    resetn = 1;
    $display("Reset released at time %0t", $time);
  end
  
  //==========================================================================
  // Interface Instances
  //==========================================================================
  picorv32_mem_if mem_if(clk, resetn);
  picorv32_irq_if irq_if(clk, resetn);
  
  //==========================================================================
  // DUT Instantiation
  //==========================================================================
  
  // Tie off unused signals
  wire [31:0] pcpi_rd = 32'h0;
  wire        pcpi_wr = 1'b0;
  wire        pcpi_wait = 1'b0;
  wire        pcpi_ready = 1'b0;
  
  // Unused outputs
  wire        mem_la_read;
  wire        mem_la_write;
  wire [31:0] mem_la_addr;
  wire [31:0] mem_la_wdata;
  wire [3:0]  mem_la_wstrb;
  wire        pcpi_valid;
  wire [31:0] pcpi_insn;
  wire [31:0] pcpi_rs1;
  wire [31:0] pcpi_rs2;
  wire        trace_valid;
  wire [35:0] trace_data;
  
  picorv32 #(
    .ENABLE_COUNTERS     (1),
    .ENABLE_COUNTERS64   (1),
    .ENABLE_REGS_16_31   (1),
    .ENABLE_REGS_DUALPORT(1),
    .LATCHED_MEM_RDATA   (0),
    .TWO_STAGE_SHIFT     (1),
    .BARREL_SHIFTER      (0),
    .TWO_CYCLE_COMPARE   (0),
    .TWO_CYCLE_ALU       (0),
    .COMPRESSED_ISA      (1),
    .CATCH_MISALIGN      (1),
    .CATCH_ILLINSN       (1),
    .ENABLE_PCPI         (0),
    .ENABLE_MUL          (1),
    .ENABLE_FAST_MUL     (0),
    .ENABLE_DIV          (1),
    .ENABLE_IRQ          (1),
    .ENABLE_IRQ_QREGS    (1),
    .ENABLE_IRQ_TIMER    (1),
    .ENABLE_TRACE        (0),
    .REGS_INIT_ZERO      (1),
    .MASKED_IRQ          (32'h0000_0000),
    .LATCHED_IRQ         (32'hffff_ffff),
    .PROGADDR_RESET      (32'h0000_0000),
    .PROGADDR_IRQ        (32'h0000_0010),
    .STACKADDR           (32'h0001_0000)
  ) dut (
    .clk            (clk),
    .resetn         (resetn),
    .trap           (mem_if.trap),
    
    // Memory interface
    .mem_valid      (mem_if.mem_valid),
    .mem_instr      (mem_if.mem_instr),
    .mem_ready      (mem_if.mem_ready),
    .mem_addr       (mem_if.mem_addr),
    .mem_wdata      (mem_if.mem_wdata),
    .mem_wstrb      (mem_if.mem_wstrb),
    .mem_rdata      (mem_if.mem_rdata),
    
    // Look-ahead interface
    .mem_la_read    (mem_la_read),
    .mem_la_write   (mem_la_write),
    .mem_la_addr    (mem_la_addr),
    .mem_la_wdata   (mem_la_wdata),
    .mem_la_wstrb   (mem_la_wstrb),
    
    // PCPI (unused)
    .pcpi_valid     (pcpi_valid),
    .pcpi_insn      (pcpi_insn),
    .pcpi_rs1       (pcpi_rs1),
    .pcpi_rs2       (pcpi_rs2),
    .pcpi_wr        (pcpi_wr),
    .pcpi_rd        (pcpi_rd),
    .pcpi_wait      (pcpi_wait),
    .pcpi_ready     (pcpi_ready),
    
    // IRQ interface
    .irq            (irq_if.irq),
    .eoi            (irq_if.eoi),
    
    // Trace (unused)
    .trace_valid    (trace_valid),
    .trace_data     (trace_data)
  );
  
  // Initialize IRQ to zero
  initial begin
    irq_if.irq = 32'h0;
  end
  
  //==========================================================================
  // UVM Configuration and Test Start
  //==========================================================================
  initial begin
    // Register interfaces in config_db
    uvm_config_db#(virtual picorv32_mem_if)::set(null, "*", "mem_vif", mem_if);
    uvm_config_db#(virtual picorv32_irq_if)::set(null, "*", "irq_vif", irq_if);
    
    // Start UVM test
    run_test();
  end
  
  //==========================================================================
  // Waveform Dump
  //==========================================================================
  initial begin
    if ($test$plusargs("dump")) begin
      $dumpfile("picorv32_tb.vcd");
      $dumpvars(0, tb_top);
      $display("Waveform dump enabled");
    end
  end
  
  //==========================================================================
  // Timeout Watchdog
  //==========================================================================
  initial begin
    #10_000_000;  // 10ms timeout
    $display("ERROR: Global timeout reached!");
    $finish;
  end
  
endmodule : tb_top
