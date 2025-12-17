// ============================================================================
// PicoRV32 Formal Verification Top Module
// ============================================================================
// This is the top-level wrapper for formal verification of PicoRV32.
// It instantiates the DUT, connects formal property modules, and provides
// the necessary infrastructure for formal tools.
//
// Usage:
//   This file is referenced by the .sby SymbiYosys configuration files.
//   Run formal verification with: sby -f picorv32.sby
// ============================================================================

`default_nettype none

module formal_top (
    input wire clk
);

    // ========================================================================
    // RESET GENERATION
    // ========================================================================
    // Formal tools need controlled reset for proper initialization
    
    reg [3:0] reset_counter = 0;
    reg resetn = 0;
    
    always @(posedge clk) begin
        if (reset_counter < 4'd5) begin
            reset_counter <= reset_counter + 1;
            resetn <= 0;
        end else begin
            resetn <= 1;
        end
    end

    // ========================================================================
    // MEMORY INTERFACE SIGNALS
    // ========================================================================
    
    wire        mem_valid;
    wire        mem_instr;
    wire        mem_ready;
    wire [31:0] mem_addr;
    wire [31:0] mem_wdata;
    wire [ 3:0] mem_wstrb;
    wire [31:0] mem_rdata;
    
    // Look-ahead interface
    wire        mem_la_read;
    wire        mem_la_write;
    wire [31:0] mem_la_addr;
    wire [31:0] mem_la_wdata;
    wire [ 3:0] mem_la_wstrb;

    // ========================================================================
    // PCPI (Pico Co-Processor Interface)
    // ========================================================================
    
    wire        pcpi_valid;
    wire [31:0] pcpi_insn;
    wire [31:0] pcpi_rs1;
    wire [31:0] pcpi_rs2;
    wire        pcpi_wr;
    wire [31:0] pcpi_rd;
    wire        pcpi_wait;
    wire        pcpi_ready;
    
    // Tie off PCPI (no co-processor for basic verification)
    assign pcpi_wr    = 1'b0;
    assign pcpi_rd    = 32'h0;
    assign pcpi_wait  = 1'b0;
    assign pcpi_ready = 1'b0;

    // ========================================================================
    // IRQ INTERFACE
    // ========================================================================
    
    wire [31:0] irq;
    wire [31:0] eoi;
    
    // Tie off IRQs for basic verification
    assign irq = 32'h0;

    // ========================================================================
    // TRACE INTERFACE
    // ========================================================================
    
    wire        trace_valid;
    wire [35:0] trace_data;

    // ========================================================================
    // PROCESSOR STATUS
    // ========================================================================
    
    wire trap;

    // ========================================================================
    // FORMAL MEMORY MODEL
    // ========================================================================
    // Simple memory model for formal verification
    // Uses symbolic (unconstrained) read data for exhaustive exploration
    
    (* anyconst *) reg [31:0] memory_content [0:255];  // Small memory for tractability
    
    // Memory read
    assign mem_rdata = memory_content[mem_addr[9:2]];
    
    // Memory ready signal - use formal input for exploring timing variations
    (* anyseq *) reg formal_mem_ready;
    
    // Constrain memory ready to be well-behaved
    reg mem_pending;
    always @(posedge clk) begin
        if (!resetn)
            mem_pending <= 0;
        else if (mem_valid && !mem_ready)
            mem_pending <= 1;
        else if (mem_ready)
            mem_pending <= 0;
    end
    
    // Memory must eventually respond
    reg [7:0] mem_wait_counter;
    always @(posedge clk) begin
        if (!resetn || !mem_valid || mem_ready)
            mem_wait_counter <= 0;
        else
            mem_wait_counter <= mem_wait_counter + 1;
    end
    
    // Force ready after timeout (prevents deadlock)
    assign mem_ready = mem_valid && (formal_mem_ready || mem_wait_counter > 8'd10);

    // ========================================================================
    // PICORV32 DUT INSTANTIATION
    // ========================================================================
    
    picorv32 #(
        // Use minimal configuration for formal tractability
        .ENABLE_COUNTERS      (0),
        .ENABLE_COUNTERS64    (0),
        .ENABLE_REGS_16_31    (1),
        .ENABLE_REGS_DUALPORT (1),
        .LATCHED_MEM_RDATA    (0),
        .TWO_STAGE_SHIFT      (1),
        .BARREL_SHIFTER       (0),
        .TWO_CYCLE_COMPARE    (0),
        .TWO_CYCLE_ALU        (0),
        .COMPRESSED_ISA       (0),
        .CATCH_MISALIGN       (1),
        .CATCH_ILLINSN        (1),
        .ENABLE_PCPI          (0),
        .ENABLE_MUL           (0),
        .ENABLE_FAST_MUL      (0),
        .ENABLE_DIV           (0),
        .ENABLE_IRQ           (0),
        .ENABLE_IRQ_QREGS     (0),
        .ENABLE_IRQ_TIMER     (0),
        .ENABLE_TRACE         (1),  // Enable for instruction-level verification
        .REGS_INIT_ZERO       (1),
        .MASKED_IRQ           (32'h0000_0000),
        .LATCHED_IRQ          (32'hffff_ffff),
        .PROGADDR_RESET       (32'h0000_0000),
        .PROGADDR_IRQ         (32'h0000_0010),
        .STACKADDR            (32'h0000_0100)
    ) dut (
        .clk            (clk),
        .resetn         (resetn),
        .trap           (trap),
        
        // Memory interface
        .mem_valid      (mem_valid),
        .mem_instr      (mem_instr),
        .mem_ready      (mem_ready),
        .mem_addr       (mem_addr),
        .mem_wdata      (mem_wdata),
        .mem_wstrb      (mem_wstrb),
        .mem_rdata      (mem_rdata),
        
        // Look-ahead interface
        .mem_la_read    (mem_la_read),
        .mem_la_write   (mem_la_write),
        .mem_la_addr    (mem_la_addr),
        .mem_la_wdata   (mem_la_wdata),
        .mem_la_wstrb   (mem_la_wstrb),
        
        // PCPI interface (unused)
        .pcpi_valid     (pcpi_valid),
        .pcpi_insn      (pcpi_insn),
        .pcpi_rs1       (pcpi_rs1),
        .pcpi_rs2       (pcpi_rs2),
        .pcpi_wr        (pcpi_wr),
        .pcpi_rd        (pcpi_rd),
        .pcpi_wait      (pcpi_wait),
        .pcpi_ready     (pcpi_ready),
        
        // IRQ interface (unused)
        .irq            (irq),
        .eoi            (eoi),
        
        // Trace interface
        .trace_valid    (trace_valid),
        .trace_data     (trace_data)
    );

    // ========================================================================
    // PROPERTY MODULE INSTANTIATION
    // ========================================================================
    
    // Main property checker
    picorv32_props props_inst (
        .clk            (clk),
        .resetn         (resetn),
        .mem_valid      (mem_valid),
        .mem_instr      (mem_instr),
        .mem_ready      (mem_ready),
        .mem_addr       (mem_addr),
        .mem_wdata      (mem_wdata),
        .mem_wstrb      (mem_wstrb),
        .mem_rdata      (mem_rdata),
        .trap           (trap),
        .pc             (mem_addr),  // Use mem_addr during ifetch as PC
        .trace_valid    (trace_valid),
        .trace_data     (trace_data)
    );
    
    // Comprehensive assertions
    picorv32_assertions assertions_inst (
        .clk            (clk),
        .resetn         (resetn),
        .mem_valid      (mem_valid),
        .mem_instr      (mem_instr),
        .mem_ready      (mem_ready),
        .mem_addr       (mem_addr),
        .mem_wdata      (mem_wdata),
        .mem_wstrb      (mem_wstrb),
        .mem_rdata      (mem_rdata),
        .mem_la_read    (mem_la_read),
        .mem_la_write   (mem_la_write),
        .mem_la_addr    (mem_la_addr),
        .mem_la_wdata   (mem_la_wdata),
        .mem_la_wstrb   (mem_la_wstrb),
        .pcpi_valid     (pcpi_valid),
        .pcpi_insn      (pcpi_insn),
        .pcpi_rs1       (pcpi_rs1),
        .pcpi_rs2       (pcpi_rs2),
        .pcpi_wr        (pcpi_wr),
        .pcpi_rd        (pcpi_rd),
        .pcpi_wait      (pcpi_wait),
        .pcpi_ready     (pcpi_ready),
        .irq            (irq),
        .eoi            (eoi),
        .trace_valid    (trace_valid),
        .trace_data     (trace_data),
        .trap           (trap)
    );

    // ========================================================================
    // ADDITIONAL FORMAL CONSTRAINTS
    // ========================================================================
    
    // Initial state constraints
    initial begin
        assume(reset_counter == 0);
    end
    
    // Fairness constraint: memory eventually responds
    // (Prevents false positive liveness failures)
`ifdef FORMAL
    always @(posedge clk) begin
        if (resetn && mem_wait_counter > 8'd5) begin
            assume(formal_mem_ready);
        end
    end
`endif

endmodule

`default_nettype wire
