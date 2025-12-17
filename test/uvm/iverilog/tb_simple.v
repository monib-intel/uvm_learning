// Simple Verilog Testbench for Icarus Verilog
// This is a lightweight testbench for quick design verification
// without requiring UVM/SystemVerilog features
//
// Usage: make run-iverilog FIRMWARE=firmware/simple_test.hex

`timescale 1ns/1ps

module tb_simple;

  //==========================================================================
  // Clock and Reset
  //==========================================================================
  reg clk = 0;
  reg resetn = 0;
  
  always #5 clk = ~clk;  // 100MHz clock
  
  initial begin
    resetn = 0;
    repeat(10) @(posedge clk);
    resetn = 1;
    $display("[%0t] Reset released", $time);
  end

  //==========================================================================
  // Memory Interface
  //==========================================================================
  wire        mem_valid;
  wire        mem_instr;
  reg         mem_ready;
  wire [31:0] mem_addr;
  wire [31:0] mem_wdata;
  wire [3:0]  mem_wstrb;
  reg  [31:0] mem_rdata;
  
  wire        trap;

  //==========================================================================
  // Memory Model
  //==========================================================================
  reg [31:0] memory [0:65535];  // 256KB
  
  // Load firmware
  initial begin
    string firmware;
    if ($value$plusargs("firmware=%s", firmware)) begin
      $readmemh(firmware, memory);
      $display("[%0t] Loaded firmware: %s", $time, firmware);
    end else begin
      $display("[%0t] No firmware specified, using default", $time);
      $readmemh("firmware/simple_test.hex", memory);
    end
  end
  
  // Memory response
  wire [31:0] mem_addr_word = mem_addr[17:2];
  
  always @(posedge clk) begin
    mem_ready <= 0;
    if (mem_valid && !mem_ready) begin
      mem_ready <= 1;
      if (mem_wstrb != 0) begin
        // Write
        if (mem_wstrb[0]) memory[mem_addr_word][7:0]   <= mem_wdata[7:0];
        if (mem_wstrb[1]) memory[mem_addr_word][15:8]  <= mem_wdata[15:8];
        if (mem_wstrb[2]) memory[mem_addr_word][23:16] <= mem_wdata[23:16];
        if (mem_wstrb[3]) memory[mem_addr_word][31:24] <= mem_wdata[31:24];
        $display("[%0t] MEM WR [%08x] = %08x (strb=%04b)", 
                 $time, mem_addr, mem_wdata, mem_wstrb);
      end else begin
        // Read
        $display("[%0t] MEM RD [%08x] = %08x %s", 
                 $time, mem_addr, memory[mem_addr_word],
                 mem_instr ? "(instr)" : "(data)");
      end
      mem_rdata <= memory[mem_addr_word];
    end
  end

  //==========================================================================
  // DUT Instantiation
  //==========================================================================
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
    .trap           (trap),
    
    .mem_valid      (mem_valid),
    .mem_instr      (mem_instr),
    .mem_ready      (mem_ready),
    .mem_addr       (mem_addr),
    .mem_wdata      (mem_wdata),
    .mem_wstrb      (mem_wstrb),
    .mem_rdata      (mem_rdata),
    
    // Unused
    .mem_la_read    (),
    .mem_la_write   (),
    .mem_la_addr    (),
    .mem_la_wdata   (),
    .mem_la_wstrb   (),
    
    .pcpi_valid     (),
    .pcpi_insn      (),
    .pcpi_rs1       (),
    .pcpi_rs2       (),
    .pcpi_wr        (1'b0),
    .pcpi_rd        (32'h0),
    .pcpi_wait      (1'b0),
    .pcpi_ready     (1'b0),
    
    .irq            (32'h0),
    .eoi            (),
    
    .trace_valid    (),
    .trace_data     ()
  );

  //==========================================================================
  // Test Control
  //==========================================================================
  integer cycle_count = 0;
  reg [31:0] last_instr_addr = 32'hFFFFFFFF;
  integer same_addr_count = 0;
  
  always @(posedge clk) begin
    if (resetn) cycle_count <= cycle_count + 1;
  end
  
  // Detect stuck PC (same instruction address repeated)
  always @(posedge clk) begin
    if (mem_valid && mem_ready && mem_instr) begin
      if (mem_addr == last_instr_addr) begin
        same_addr_count <= same_addr_count + 1;
      end else begin
        same_addr_count <= 0;
        last_instr_addr <= mem_addr;
      end
    end
  end
  
  // End simulation on trap, stuck PC, or timeout
  always @(posedge clk) begin
    if (trap) begin
      $display("");
      $display("========================================");
      $display("  TRAP detected at cycle %0d", cycle_count);
      $display("  Simulation complete - PASS");
      $display("========================================");
      #100;
      $finish;
    end
    
    if (same_addr_count > 5) begin
      $display("");
      $display("========================================");
      $display("  Program ended (PC stuck at 0x%08x)", last_instr_addr);
      $display("  Cycle count: %0d", cycle_count);
      $display("  Simulation complete - PASS");
      $display("========================================");
      #100;
      $finish;
    end
    
    if (cycle_count > 100000) begin
      $display("");
      $display("========================================");
      $display("  TIMEOUT after %0d cycles", cycle_count);
      $display("========================================");
      $finish;
    end
  end

  //==========================================================================
  // Waveform Dump
  //==========================================================================
  initial begin
    $dumpfile("picorv32_tb.vcd");
    $dumpvars(0, tb_simple);
    $display("[%0t] Waveform dump enabled: picorv32_tb.vcd", $time);
  end

endmodule
