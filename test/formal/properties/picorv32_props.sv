// ============================================================================
// PicoRV32 Formal Verification Properties
// ============================================================================
// This file contains the core SVA properties for formally verifying the 
// PicoRV32 RISC-V processor. Properties are organized by category:
// - Safety properties (bad things never happen)
// - Liveness properties (good things eventually happen)  
// - Protocol properties (interface compliance)
// - Functional properties (correct operation)
//
// Usage with SymbiYosys:
//   Include this file in your .sby configuration
//   Run: sby -f picorv32.sby
// ============================================================================

`default_nettype none

module picorv32_props (
    // Note: Package import removed for Yosys/SymbiYosys compatibility
    // Use explicit parameters instead
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
    
    // Processor State
    input wire        trap,
    input wire [31:0] pc,
    
    // Optional: Trace interface for deeper verification
    input wire        trace_valid,
    input wire [35:0] trace_data
);

// ============================================================================
// SECTION 1: SAFETY PROPERTIES
// "Bad things never happen"
// ============================================================================

// ---------------------------------------------------------------------------
// Property: PC must be word-aligned during instruction fetch
// Rationale: RISC-V instructions are 4-byte aligned (32-bit mode)
// ---------------------------------------------------------------------------
property pc_word_aligned_on_fetch;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && mem_instr) |-> (mem_addr[1:0] == 2'b00);
endproperty

assert property (pc_word_aligned_on_fetch)
    else $error("[FORMAL] PC not word-aligned: addr=0x%08h", mem_addr);

// ---------------------------------------------------------------------------
// Property: Memory address must be within valid range
// Rationale: Prevent access to undefined memory regions
// ---------------------------------------------------------------------------
property mem_addr_in_range;
    @(posedge clk) disable iff (!resetn)
    mem_valid |-> (mem_addr < 32'hFFFF_0000);  // Example: top 64KB reserved
endproperty

assert property (mem_addr_in_range)
    else $error("[FORMAL] Memory access out of range: addr=0x%08h", mem_addr);

// ---------------------------------------------------------------------------
// Property: Write strobe must be valid pattern for store instructions
// Rationale: Only valid byte/halfword/word patterns allowed
// ---------------------------------------------------------------------------
property wstrb_valid_pattern;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && |mem_wstrb) |-> 
        (mem_wstrb inside {
            4'b0001, 4'b0010, 4'b0100, 4'b1000,  // Byte stores
            4'b0011, 4'b1100,                      // Halfword stores
            4'b1111                                // Word stores
        });
endproperty

assert property (wstrb_valid_pattern)
    else $error("[FORMAL] Invalid write strobe pattern: wstrb=0x%01h", mem_wstrb);

// ---------------------------------------------------------------------------
// Property: No write strobe during instruction fetch
// Rationale: Instruction fetches are always reads
// ---------------------------------------------------------------------------
property no_write_on_ifetch;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && mem_instr) |-> (mem_wstrb == 4'b0000);
endproperty

assert property (no_write_on_ifetch)
    else $error("[FORMAL] Write strobe active during instruction fetch!");

// ---------------------------------------------------------------------------
// Property: Trap signal is stable after assertion (until reset)
// Rationale: Once trapped, processor stops until reset
// ---------------------------------------------------------------------------
property trap_is_sticky;
    @(posedge clk) disable iff (!resetn)
    trap |=> trap;
endproperty

// Note: This property may not hold for all PicoRV32 configurations
// Uncomment if using CATCH_ILLINSN or CATCH_MISALIGN
// assert property (trap_is_sticky);

// ============================================================================
// SECTION 2: PROTOCOL PROPERTIES  
// Interface compliance and handshake verification
// ============================================================================

// ---------------------------------------------------------------------------
// Property: Memory request signals must be stable until acknowledged
// Rationale: AXI-like protocol requires signal stability during transaction
// ---------------------------------------------------------------------------
property mem_valid_stable_until_ready;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && !mem_ready) |=> mem_valid;
endproperty

assert property (mem_valid_stable_until_ready)
    else $error("[FORMAL] mem_valid deasserted before mem_ready!");

property mem_addr_stable_until_ready;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && !mem_ready) |=> $stable(mem_addr);
endproperty

assert property (mem_addr_stable_until_ready)
    else $error("[FORMAL] mem_addr changed during pending transaction!");

property mem_wdata_stable_until_ready;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && !mem_ready && |mem_wstrb) |=> $stable(mem_wdata);
endproperty

assert property (mem_wdata_stable_until_ready)
    else $error("[FORMAL] mem_wdata changed during pending write!");

property mem_wstrb_stable_until_ready;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && !mem_ready) |=> $stable(mem_wstrb);
endproperty

assert property (mem_wstrb_stable_until_ready)
    else $error("[FORMAL] mem_wstrb changed during pending transaction!");

property mem_instr_stable_until_ready;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && !mem_ready) |=> $stable(mem_instr);
endproperty

assert property (mem_instr_stable_until_ready)
    else $error("[FORMAL] mem_instr changed during pending transaction!");

// ---------------------------------------------------------------------------
// Property: After transaction completes, valid should deassert (eventually)
// Rationale: Prevents bus hogging
// ---------------------------------------------------------------------------
property valid_deasserts_after_ready;
    @(posedge clk) disable iff (!resetn)
    (mem_valid && mem_ready) |=> ##[0:5] !mem_valid;
endproperty

// This is a soft property - may not always hold, useful for checking
// assert property (valid_deasserts_after_ready);

// ============================================================================
// SECTION 3: COVER PROPERTIES
// Verify that interesting scenarios are reachable
// ============================================================================

// ---------------------------------------------------------------------------
// Cover: Instruction fetch from various memory regions
// ---------------------------------------------------------------------------
cover property (@(posedge clk) disable iff (!resetn)
    mem_valid && mem_instr && mem_addr == 32'h0000_0000);
    // Boot from reset vector

cover property (@(posedge clk) disable iff (!resetn)
    mem_valid && mem_instr && mem_addr[31:16] == 16'h0001);
    // Fetch from higher memory

// ---------------------------------------------------------------------------
// Cover: Different store types
// ---------------------------------------------------------------------------
cover property (@(posedge clk) disable iff (!resetn)
    mem_valid && mem_wstrb == 4'b0001);
    // Byte store

cover property (@(posedge clk) disable iff (!resetn)
    mem_valid && mem_wstrb == 4'b0011);
    // Halfword store

cover property (@(posedge clk) disable iff (!resetn)
    mem_valid && mem_wstrb == 4'b1111);
    // Word store

// ---------------------------------------------------------------------------
// Cover: Trap condition
// ---------------------------------------------------------------------------
cover property (@(posedge clk) disable iff (!resetn)
    $rose(trap));
    // Trap signal raised

// ============================================================================
// SECTION 4: HELPER LOGIC FOR FORMAL
// ============================================================================

// Counter for tracking cycles since reset
reg [15:0] cycle_count;
always @(posedge clk) begin
    if (!resetn)
        cycle_count <= 0;
    else if (cycle_count < 16'hFFFF)
        cycle_count <= cycle_count + 1;
end

// Track pending transactions
reg transaction_pending;
always @(posedge clk) begin
    if (!resetn)
        transaction_pending <= 0;
    else if (mem_valid && !mem_ready)
        transaction_pending <= 1;
    else if (mem_ready)
        transaction_pending <= 0;
end

// ---------------------------------------------------------------------------
// Property: No new transaction while one is pending
// Rationale: Simple memory interface allows only one outstanding transaction
// ---------------------------------------------------------------------------
// Note: This may not be accurate for pipelined memory interfaces
// property no_overlapping_transactions;
//     @(posedge clk) disable iff (!resetn)
//     transaction_pending |-> mem_valid;
// endproperty

endmodule

`default_nettype wire
