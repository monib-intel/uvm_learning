// ============================================================================
// PicoRV32 SVA Tutorial Examples
// ============================================================================
// This file provides comprehensive examples of SystemVerilog Assertions (SVA)
// for learning purposes. It demonstrates:
// - Immediate assertions
// - Concurrent assertions  
// - Sequences and properties
// - Temporal operators
// - System functions
// - Local variables
//
// Reference: IEEE 1800-2017, Section 16 (Assertions)
// ============================================================================

`default_nettype none

module picorv32_sva_tutorial (
    input wire        clk,
    input wire        resetn,
    
    // Example signals for demonstration
    input wire        req,
    input wire        ack,
    input wire        grant,
    input wire        busy,
    input wire        valid,
    input wire        ready,
    input wire [31:0] data,
    input wire [31:0] addr,
    input wire [ 3:0] wstrb,
    input wire        error
);

// ============================================================================
// SECTION 1: IMMEDIATE ASSERTIONS
// Checked at a specific point in simulation/formal time
// ============================================================================

// Basic immediate assertion
always @(posedge clk) begin
    if (resetn) begin
        // Assert that if we're writing, address must be word-aligned
        immediate_word_aligned: assert (|wstrb == 0 || addr[1:0] == 2'b00)
            else $error("Write to unaligned address: 0x%08h", addr);
    end
end

// Immediate assertion with pass action
always @(posedge clk) begin
    if (resetn && valid) begin
        immediate_data_valid: assert (!$isunknown(data))
            $display("Data is valid: 0x%08h", data);
            else $error("Data contains X/Z during valid!");
    end
end

// Immediate assume (for formal - treated as assert in simulation)
always @(posedge clk) begin
    if (resetn) begin
        assume_no_simultaneous: assume (!(req && grant))
            else $warning("Unexpected: req and grant simultaneous");
    end
end

// Immediate cover (tracks reachability)
always @(posedge clk) begin
    if (resetn) begin
        cover_high_address: cover (addr > 32'h8000_0000)
            $display("[COVER] High address access: 0x%08h", addr);
    end
end

// ============================================================================
// SECTION 2: BASIC CONCURRENT ASSERTIONS
// Checked continuously over clock cycles
// ============================================================================

// Simple property: valid implies ready eventually
property valid_then_ready;
    @(posedge clk) disable iff (!resetn)
    valid |-> ##[1:10] ready;
endproperty

assert property (valid_then_ready)
    else $error("Ready not asserted within 10 cycles of valid!");

// Request-Acknowledge handshake
property req_ack_handshake;
    @(posedge clk) disable iff (!resetn)
    req |-> ##[1:5] ack;
endproperty

assert property (req_ack_handshake)
    else $error("No ack within 5 cycles of req!");

// Mutual exclusion
property mutual_exclusion;
    @(posedge clk) disable iff (!resetn)
    !(req && grant);  // Never both high simultaneously
endproperty

assert property (mutual_exclusion)
    else $error("Mutual exclusion violated!");

// ============================================================================
// SECTION 3: TEMPORAL OPERATORS
// ============================================================================

// ##n - Fixed delay
property fixed_delay;
    @(posedge clk) disable iff (!resetn)
    req |-> ##3 ack;  // Exactly 3 cycles later
endproperty

// ##[m:n] - Range delay
property range_delay;
    @(posedge clk) disable iff (!resetn)
    req |-> ##[1:5] ack;  // 1 to 5 cycles later
endproperty

// ##[0:$] - Zero to unbounded
property eventually;
    @(posedge clk) disable iff (!resetn)
    req |-> ##[0:$] ack;  // Eventually (but might take forever - use carefully!)
endproperty

// |-> Overlapping implication (same cycle)
property overlapping;
    @(posedge clk) disable iff (!resetn)
    valid |-> ready;  // If valid, ready must also be high THIS cycle
endproperty

// |=> Non-overlapping implication (next cycle)
property non_overlapping;
    @(posedge clk) disable iff (!resetn)
    req |=> grant;  // If req this cycle, grant NEXT cycle
endproperty

// ============================================================================
// SECTION 4: REPETITION OPERATORS
// ============================================================================

// [*n] - Consecutive repetition
property three_consecutive;
    @(posedge clk) disable iff (!resetn)
    valid[*3] |-> ready;  // After 3 consecutive valids, ready
endproperty

// [*m:n] - Repetition range
property one_to_four_busy;
    @(posedge clk) disable iff (!resetn)
    req ##1 busy[*1:4] ##1 grant;  // 1-4 busy cycles between req and grant
endproperty

// [*0:n] - Zero or more
property optional_busy;
    @(posedge clk) disable iff (!resetn)
    req ##1 busy[*0:3] ##1 grant;  // 0-3 busy cycles (optional)
endproperty

// [->n] - Goto repetition (non-consecutive)
property goto_repetition;
    @(posedge clk) disable iff (!resetn)
    req |-> valid[->3] ##1 ready;  // 3 valids (not necessarily consecutive), then ready
endproperty

// [=n] - Non-consecutive exact
property nonconsec_exact;
    @(posedge clk) disable iff (!resetn)
    req |-> ack[=2] ##1 ready;  // Exactly 2 acks (non-consecutive), then ready
endproperty

// ============================================================================
// SECTION 5: EDGE DETECTION AND VALUE CHANGE
// ============================================================================

// $rose - Rising edge detection
property detect_rising;
    @(posedge clk) disable iff (!resetn)
    $rose(valid) |-> ##[1:3] ready;
endproperty

assert property (detect_rising)
    else $error("Ready not asserted within 3 cycles of valid rising!");

// $fell - Falling edge detection
property detect_falling;
    @(posedge clk) disable iff (!resetn)
    $fell(busy) |-> grant;  // When busy falls, grant should be high
endproperty

// $stable - No change
property data_stable_during_valid;
    @(posedge clk) disable iff (!resetn)
    (valid && !ready) |=> $stable(data);  // Data stable while waiting
endproperty

assert property (data_stable_during_valid)
    else $error("Data changed while valid asserted!");

// $changed - Value changed
property addr_changes;
    @(posedge clk) disable iff (!resetn)
    (valid && ready) |=> $changed(addr) || !valid;
endproperty

// $past - Previous value
property check_previous;
    @(posedge clk) disable iff (!resetn)
    ready |-> ($past(valid, 1) || $past(valid, 2));  // ready requires valid 1 or 2 cycles ago
endproperty

// ============================================================================
// SECTION 6: NAMED SEQUENCES
// Reusable sequence definitions
// ============================================================================

// Simple named sequence
sequence req_grant_seq;
    req ##[1:3] grant;
endsequence

// Parameterized sequence
sequence delay_seq(sig, min_delay, max_delay);
    sig ##[min_delay:max_delay] !sig;
endsequence

// Sequence using another sequence
sequence full_handshake;
    req ##1 busy[*0:5] ##1 req_grant_seq ##1 ack;
endsequence

// Property using named sequences
property handshake_completes;
    @(posedge clk) disable iff (!resetn)
    full_handshake;
endproperty

// ============================================================================
// SECTION 7: SEQUENCE OPERATORS
// ============================================================================

// and - Both sequences match (same start point)
sequence seq_and;
    (req ##[1:3] grant) and (valid ##[1:3] ready);
endsequence

// or - Either sequence matches
sequence seq_or;
    (req ##1 grant) or (req ##2 grant) or (req ##3 grant);
endsequence

// intersect - Both match with same length
sequence seq_intersect;
    (valid ##[1:5] ready) intersect (busy[*3:7]);
endsequence

// within - First completes within second
sequence seq_within;
    (valid ##1 ready) within (busy[*5]);
endsequence

// throughout - Condition holds during sequence
sequence seq_throughout;
    !error throughout (req ##[1:10] ack);
endsequence

property no_error_during_handshake;
    @(posedge clk) disable iff (!resetn)
    req |-> seq_throughout;
endproperty

// first_match - Only first matching trace
property use_first_match;
    @(posedge clk) disable iff (!resetn)
    first_match(req ##[1:100] ack) |-> ready;
endproperty

// ============================================================================
// SECTION 8: LOCAL VARIABLES IN SEQUENCES
// Capture values for later comparison
// ============================================================================

// Capture and compare
sequence capture_data;
    logic [31:0] captured;
    (valid, captured = data) ##[1:5] (ready && data == captured);
endsequence

property data_preserved;
    @(posedge clk) disable iff (!resetn)
    capture_data;
endproperty

// Multiple captures
sequence multi_capture;
    logic [31:0] cap_addr, cap_data;
    (valid, cap_addr = addr, cap_data = data) 
    ##[1:10] 
    (ready && addr == cap_addr && data == cap_data);
endsequence

// Increment check
sequence check_increment;
    logic [31:0] initial_val;
    (valid, initial_val = data) ##1 (data == initial_val + 1);
endsequence

// ============================================================================
// SECTION 9: SYSTEM FUNCTIONS FOR ASSERTIONS
// ============================================================================

// $onehot - Exactly one bit set
property addr_onehot;
    @(posedge clk) disable iff (!resetn)
    valid |-> $onehot(wstrb) || wstrb == 4'b0000 || wstrb == 4'b1111;
endproperty

// $onehot0 - At most one bit set
property state_onehot0;
    @(posedge clk) disable iff (!resetn)
    $onehot0({req, grant, ack});  // At most one active
endproperty

// $countones - Count set bits
property wstrb_count;
    @(posedge clk) disable iff (!resetn)
    valid |-> $countones(wstrb) inside {0, 1, 2, 4};  // Valid byte patterns
endproperty

// $isunknown - Check for X/Z
property no_x_on_data;
    @(posedge clk) disable iff (!resetn)
    valid |-> !$isunknown(data);
endproperty

assert property (no_x_on_data)
    else $error("X/Z detected on data bus during valid!");

// ============================================================================
// SECTION 10: COVER PROPERTIES
// Check reachability of scenarios
// ============================================================================

// Simple covers
cover property (@(posedge clk) disable iff (!resetn) req && ack);
cover property (@(posedge clk) disable iff (!resetn) $rose(valid));
cover property (@(posedge clk) disable iff (!resetn) addr > 32'h1000_0000);

// Cover sequences
cover property (@(posedge clk) disable iff (!resetn) 
    req ##1 busy[*3] ##1 grant);

// Cover with action
cover property (@(posedge clk) disable iff (!resetn)
    valid ##[5:10] ready)
    $display("[COVER] Slow ready response observed");

// ============================================================================
// SECTION 11: ASSUMPTIONS (FOR FORMAL)
// Constrain environment inputs
// ============================================================================

// Basic assumption
assume property (@(posedge clk) disable iff (!resetn)
    $rose(req) |-> ##[0:20] $fell(req));  // req always deasserts within 20 cycles

// Mutual exclusion assumption
assume property (@(posedge clk) disable iff (!resetn)
    !(valid && error));  // valid and error never simultaneous

// Data range assumption
assume property (@(posedge clk) disable iff (!resetn)
    valid |-> addr < 32'hFFFF_0000);  // Address within valid range

// Response timing assumption
assume property (@(posedge clk) disable iff (!resetn)
    req |-> ##[1:50] ack);  // Environment guarantees ack

endmodule

`default_nettype wire
