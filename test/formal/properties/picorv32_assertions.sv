// ============================================================================
// PicoRV32 SVA Assertions Library
// ============================================================================
// This file contains a comprehensive collection of SystemVerilog Assertions
// (SVA) for verifying the PicoRV32 RISC-V processor. These assertions can
// be used with both formal verification tools and simulation.
//
// SVA Assertion Types:
// 1. Immediate Assertions  - Checked at a specific simulation time
// 2. Concurrent Assertions - Checked continuously over clock cycles
// 3. Cover Properties      - Check reachability of scenarios
// 4. Assume Properties     - Constrain input behavior
//
// Reference: IEEE 1800-2017 (SystemVerilog LRM), Section 16 (Assertions)
// ============================================================================

`default_nettype none

module picorv32_assertions (
    // Note: Package import removed for Yosys/SymbiYosys compatibility
    input wire        clk,
    input wire        resetn,
    
    // Memory Interface
    input wire        mem_valid,
    input wire        mem_instr,
    input wire        mem_ready,
    input wire [31:0] mem_addr,
    input wire [31:0] mem_wdata,
    input wire [ 3:0] mem_wstrb,
    input wire [31:0] mem_rdata,
    
    // Look-Ahead Interface (optional)
    input wire        mem_la_read,
    input wire        mem_la_write,
    input wire [31:0] mem_la_addr,
    input wire [31:0] mem_la_wdata,
    input wire [ 3:0] mem_la_wstrb,
    
    // Pico Co-Processor Interface (PCPI)
    input wire        pcpi_valid,
    input wire [31:0] pcpi_insn,
    input wire [31:0] pcpi_rs1,
    input wire [31:0] pcpi_rs2,
    input wire        pcpi_wr,
    input wire [31:0] pcpi_rd,
    input wire        pcpi_wait,
    input wire        pcpi_ready,
    
    // IRQ Interface
    input wire [31:0] irq,
    input wire [31:0] eoi,
    
    // Trace Interface
    input wire        trace_valid,
    input wire [35:0] trace_data,
    
    // Status
    input wire        trap
);

// ============================================================================
// SECTION 1: IMMEDIATE ASSERTIONS
// Checked at specific points during simulation
// ============================================================================

// These would typically be placed inside procedural blocks
// Example usage in testbench:
/*
always @(posedge clk) begin
    if (resetn && mem_valid) begin
        // Immediate assertion - checked when this line executes
        assert (mem_addr[1:0] == 2'b00 || !mem_instr)
            else $error("Misaligned instruction fetch!");
    end
end
*/

// ============================================================================
// SECTION 2: CONCURRENT ASSERTIONS - SAFETY PROPERTIES
// "Bad things never happen"
// ============================================================================

// ---------------------------------------------------------------------------
// Memory Interface Safety Properties
// ---------------------------------------------------------------------------

// S1: No memory access when in reset
property no_mem_access_in_reset;
    @(posedge clk)
    !resetn |-> !mem_valid;
endproperty
assert property (no_mem_access_in_reset)
    else $error("[S1] Memory access during reset!");

// S2: Word-aligned instruction fetches
property aligned_ifetch;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && mem_instr) |-> (mem_addr[1:0] == 2'b00);
endproperty
assert property (aligned_ifetch)
    else $error("[S2] Misaligned instruction fetch at 0x%08h", mem_addr);

// S3: Valid write strobe patterns
property valid_wstrb;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && |mem_wstrb) |-> 
        mem_wstrb inside {4'b0001, 4'b0010, 4'b0100, 4'b1000,   // SB
                          4'b0011, 4'b1100,                       // SH
                          4'b1111};                               // SW
endproperty
assert property (valid_wstrb)
    else $error("[S3] Invalid write strobe: 0x%01h", mem_wstrb);

// S4: Halfword stores must be halfword-aligned
property aligned_halfword_store;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && mem_wstrb inside {4'b0011, 4'b1100}) |-> 
        (mem_addr[0] == 1'b0);
endproperty
assert property (aligned_halfword_store)
    else $error("[S4] Misaligned halfword store at 0x%08h", mem_addr);

// S5: Word stores must be word-aligned  
property aligned_word_store;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && mem_wstrb == 4'b1111) |-> 
        (mem_addr[1:0] == 2'b00);
endproperty
assert property (aligned_word_store)
    else $error("[S5] Misaligned word store at 0x%08h", mem_addr);

// S6: No write strobe during instruction fetch
property no_write_during_ifetch;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && mem_instr) |-> (mem_wstrb == 4'b0000);
endproperty
assert property (no_write_during_ifetch)
    else $error("[S6] Write strobe active during instruction fetch!");

// ============================================================================
// SECTION 3: CONCURRENT ASSERTIONS - PROTOCOL PROPERTIES
// Interface handshake compliance
// ============================================================================

// P1: mem_valid stable until mem_ready
property valid_stable;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && !mem_ready) |=> mem_valid;
endproperty
assert property (valid_stable)
    else $error("[P1] mem_valid dropped before mem_ready!");

// P2: mem_addr stable during transaction
property addr_stable;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && !mem_ready) |=> $stable(mem_addr);
endproperty
assert property (addr_stable)
    else $error("[P2] mem_addr changed during pending transaction!");

// P3: mem_wdata stable during write transaction
property wdata_stable;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && !mem_ready && |mem_wstrb) |=> $stable(mem_wdata);
endproperty
assert property (wdata_stable)
    else $error("[P3] mem_wdata changed during pending write!");

// P4: mem_wstrb stable during transaction
property wstrb_stable;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && !mem_ready) |=> $stable(mem_wstrb);
endproperty
assert property (wstrb_stable)
    else $error("[P4] mem_wstrb changed during pending transaction!");

// P5: mem_instr stable during transaction
property instr_stable;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && !mem_ready) |=> $stable(mem_instr);
endproperty
assert property (instr_stable)
    else $error("[P5] mem_instr changed during pending transaction!");

// ============================================================================
// SECTION 4: PCPI INTERFACE ASSERTIONS
// ============================================================================

// PCPI1: PCPI signals valid only when pcpi_valid is asserted
property pcpi_signals_valid;
    @(posedge clk) disable iff (!resetn)
    !pcpi_valid |-> (!pcpi_wr && !pcpi_wait && !pcpi_ready);
endproperty
// Note: This depends on co-processor implementation
// assert property (pcpi_signals_valid);

// PCPI2: PCPI ready implies pcpi_valid was recently asserted
property pcpi_ready_follows_valid;
    @(posedge clk) disable iff (!resetn)
    pcpi_ready |-> (pcpi_valid || $past(pcpi_valid));
endproperty
// assert property (pcpi_ready_follows_valid);

// PCPI3: PCPI instruction stable while waiting
property pcpi_insn_stable_during_wait;
    @(posedge clk) disable iff (!resetn)
    (pcpi_valid && pcpi_wait) |=> $stable(pcpi_insn);
endproperty
assert property (pcpi_insn_stable_during_wait)
    else $error("[PCPI3] PCPI instruction changed while waiting!");

// ============================================================================
// SECTION 5: IRQ INTERFACE ASSERTIONS
// ============================================================================

// IRQ1: EOI only for active interrupts
// (End-of-interrupt should only be raised for interrupts that were pending)
// This is implementation specific

// IRQ2: IRQ lines stable during handler execution
// (Depends on system design)

// ============================================================================
// SECTION 6: LIVENESS PROPERTIES
// "Good things eventually happen"
// Note: These require bounded checking or fairness assumptions
// ============================================================================

// L1: Memory request eventually completes
// (Requires environment assumption that memory responds)
sequence mem_request;
    mem_valid && !mem_ready;
endsequence

property mem_request_completes;
    @(posedge clk) disable iff (!resetn)
    mem_request |-> ##[1:100] mem_ready;
endproperty
// Note: This requires an assumption about memory response time
// assert property (mem_request_completes);

// L2: Processor makes progress (not stuck)
// (Would need instruction count tracking)

// ============================================================================
// SECTION 7: COVER PROPERTIES
// Verify reachability of interesting scenarios
// ============================================================================

// C1: Instruction fetch occurs
cover property (@(posedge clk) disable iff (!resetn)
    mem_valid && mem_instr && mem_ready)
    $display("[COVER] Instruction fetch completed at addr 0x%08h", mem_addr);

// C2: Data read occurs
cover property (@(posedge clk) disable iff (!resetn)
    mem_valid && !mem_instr && mem_wstrb == 0 && mem_ready)
    $display("[COVER] Data read completed at addr 0x%08h", mem_addr);

// C3: Data write occurs
cover property (@(posedge clk) disable iff (!resetn)
    mem_valid && !mem_instr && |mem_wstrb && mem_ready)
    $display("[COVER] Data write completed at addr 0x%08h", mem_addr);

// C4: Different store sizes
cover property (@(posedge clk) disable iff (!resetn)
    mem_valid && mem_wstrb == 4'b0001 && mem_ready);  // Byte store

cover property (@(posedge clk) disable iff (!resetn)
    mem_valid && mem_wstrb == 4'b0011 && mem_ready);  // Halfword store

cover property (@(posedge clk) disable iff (!resetn)
    mem_valid && mem_wstrb == 4'b1111 && mem_ready);  // Word store

// C5: Trap condition reached
cover property (@(posedge clk) disable iff (!resetn)
    $rose(trap))
    $display("[COVER] Trap asserted!");

// C6: Trace output generated
cover property (@(posedge clk) disable iff (!resetn)
    trace_valid)
    $display("[COVER] Trace output: 0x%09h", trace_data);

// C7: PCPI coprocessor interaction
cover property (@(posedge clk) disable iff (!resetn)
    pcpi_valid && pcpi_ready)
    $display("[COVER] PCPI instruction completed");

// C8: Multiple outstanding scenarios (if supported)
cover property (@(posedge clk) disable iff (!resetn)
    mem_valid ##1 mem_valid[*5]);  // 5 consecutive valid cycles

// ============================================================================
// SECTION 8: ENVIRONMENT ASSUMPTIONS
// Constrain inputs for formal verification
// ============================================================================

// A1: Memory responds within bounded time
assume property (@(posedge clk) disable iff (!resetn)
    mem_valid |-> ##[1:50] mem_ready);

// A2: Reset is applied at start
assume property (@(posedge clk)
    ($time == 0) |-> !resetn);

// A3: No spurious memory ready without valid
assume property (@(posedge clk) disable iff (!resetn)
    mem_ready |-> mem_valid);

// A4: Memory read data stable during transaction
assume property (@(posedge clk) disable iff (!resetn)
    (mem_valid && !mem_ready && mem_wstrb == 0) |=> $stable(mem_rdata));

// A5: IRQ inputs well-behaved (optional - for simplification)
// assume property (@(posedge clk) disable iff (!resetn)
//     irq == 32'h0);  // No interrupts for basic verification

// ============================================================================
// SECTION 9: HELPER SEQUENCES AND PROPERTIES
// Reusable building blocks for complex assertions
// ============================================================================

// Sequence: Complete memory transaction
sequence mem_transaction;
    mem_valid ##[1:$] (mem_valid && mem_ready);
endsequence

// Sequence: Instruction fetch
sequence ifetch;
    mem_valid && mem_instr;
endsequence

// Sequence: Data access (load or store)
sequence data_access;
    mem_valid && !mem_instr;
endsequence

// Sequence: Store operation
sequence store_op;
    mem_valid && !mem_instr && |mem_wstrb;
endsequence

// Sequence: Load operation
sequence load_op;
    mem_valid && !mem_instr && mem_wstrb == 0;
endsequence

// Property: Transaction completes in N cycles
property txn_completes_in_n(int n);
    @(posedge clk) disable iff (!resetn)
    mem_valid |-> ##[1:n] mem_ready;
endproperty

// ============================================================================
// SECTION 10: FUNCTIONAL PROPERTIES (Instruction-Specific)
// These require access to internal signals or trace interface
// ============================================================================

// Decode trace_data format (from PicoRV32):
// trace_data[35]    = trap
// trace_data[34:32] = reserved
// trace_data[31:0]  = PC or register value

wire        trace_is_trap  = trace_data[35];
wire [31:0] trace_pc       = trace_data[31:0];

// F1: Trap in trace matches trap signal
property trace_trap_consistent;
    @(posedge clk) disable iff (!resetn)
    trace_valid |-> (trace_is_trap == trap);
endproperty
// Note: May need timing adjustment
// assert property (trace_trap_consistent);

// F2: PC in trace matches instruction fetch address
// (Would require tracking the instruction fetch)

endmodule

`default_nettype wire
