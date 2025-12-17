// PicoRV32 Scoreboard
//
// The UVM Scoreboard compares actual DUT behavior against expected results.
// It receives transactions from monitors and performs correctness checking.
//
// SCOREBOARD RESPONSIBILITIES:
//   1. Receive observed transactions via analysis exports
//   2. Predict expected behavior (reference model)
//   3. Compare actual vs expected results
//   4. Track and report errors
//   5. Collect statistics for test summary
//
// SCOREBOARD ARCHITECTURE:
// ┌──────────────────────────────────────────────────────────────┐
// │                       Scoreboard                             │
// │  ┌─────────────────────────────────────────────────────┐    │
// │  │              Analysis Exports                        │    │
// │  │  (receive transactions from monitors)                │    │
// │  └───────────────────────┬─────────────────────────────┘    │
// │                          │                                   │
// │                          ▼                                   │
// │  ┌─────────────────────────────────────────────────────┐    │
// │  │              write() function                        │    │
// │  │  - Called for each received transaction              │    │
// │  │  - Routes to appropriate checker                     │    │
// │  └───────────────────────┬─────────────────────────────┘    │
// │                          │                                   │
// │            ┌─────────────┼─────────────┐                     │
// │            ▼             ▼             ▼                     │
// │     ┌───────────┐ ┌───────────┐ ┌───────────┐               │
// │     │ Instr     │ │ Data Read │ │ Data Write│               │
// │     │ Checker   │ │ Checker   │ │ Checker   │               │
// │     └───────────┘ └───────────┘ └───────────┘               │
// └──────────────────────────────────────────────────────────────┘
//
// KEY UVM CONCEPTS:
//
// 1. uvm_analysis_imp (Analysis Implementation)
//    - Implements the subscriber side of analysis port
//    - Template parameters: transaction type, parent class
//    - Parent class must implement write() function
//
// 2. WRITE FUNCTION
//    - Called automatically when monitor broadcasts transaction
//    - Non-blocking: should not consume simulation time
//    - Performs immediate checking or queues for later
//
// 3. REFERENCE MODEL INTEGRATION
//    - For RISC-V: Compare against ISS (Instruction Set Simulator)
//    - Spike, QEMU, or custom golden model
//    - Predict register file, memory state, PC progression
//
// 4. CHECK_PHASE
//    - Called at end of simulation
//    - Perform final consistency checks
//    - Report any unmatched transactions
//
// 5. REPORT_PHASE
//    - Print test summary with statistics
//    - Final pass/fail determination
//
//============================================================================

class picorv32_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(picorv32_scoreboard)
  
  // Analysis exports
  uvm_analysis_imp #(picorv32_mem_txn, picorv32_scoreboard) mem_export;
  
  // Statistics
  int unsigned num_instructions;
  int unsigned num_data_reads;
  int unsigned num_data_writes;
  int unsigned num_errors;
  int unsigned num_warnings;
  
  // Instruction tracking
  logic [31:0] last_pc;
  logic [31:0] instr_count;
  
  // Expected behavior (simple checks)
  logic [31:0] expected_next_pc;
  
  // Constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
    mem_export = new("mem_export", this);
  endfunction
  
  // Build phase
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    num_instructions = 0;
    num_data_reads   = 0;
    num_data_writes  = 0;
    num_errors       = 0;
    num_warnings     = 0;
    last_pc          = 32'h0;
    instr_count      = 0;
  endfunction
  
  // Write function - called when monitor broadcasts a transaction
  function void write(picorv32_mem_txn txn);
    if (txn.is_instr) begin
      check_instruction_fetch(txn);
    end else if (txn.is_write) begin
      check_data_write(txn);
    end else begin
      check_data_read(txn);
    end
  endfunction
  
  // Check instruction fetch
  function void check_instruction_fetch(picorv32_mem_txn txn);
    logic [6:0] opcode;
    string      instr_name;
    
    num_instructions++;
    opcode = txn.data[6:0];
    
    // Decode instruction for logging
    case (opcode)
      7'b0110111: instr_name = "LUI";
      7'b0010111: instr_name = "AUIPC";
      7'b1101111: instr_name = "JAL";
      7'b1100111: instr_name = "JALR";
      7'b1100011: instr_name = "BRANCH";
      7'b0000011: instr_name = "LOAD";
      7'b0100011: instr_name = "STORE";
      7'b0010011: instr_name = "OP-IMM";
      7'b0110011: instr_name = "OP";
      7'b0001111: instr_name = "FENCE";
      7'b1110011: instr_name = "SYSTEM";
      default:    instr_name = "UNKNOWN";
    endcase
    
    `uvm_info("SCB", $sformatf("INSTR[%0d] PC=0x%08x: 0x%08x (%s)", 
              num_instructions, txn.addr, txn.data, instr_name), UVM_HIGH)
    
    // Check for illegal instruction (all zeros or all ones)
    if (txn.data == 32'h0 || txn.data == 32'hFFFFFFFF) begin
      `uvm_warning("SCB", $sformatf("Potentially illegal instruction at PC=0x%08x: 0x%08x",
                   txn.addr, txn.data))
      num_warnings++;
    end
    
    // Track PC progression
    if (num_instructions > 1) begin
      // Simple check: PC should change (not stuck)
      if (txn.addr == last_pc && num_instructions > 10) begin
        `uvm_error("SCB", $sformatf("PC appears stuck at 0x%08x", txn.addr))
        num_errors++;
      end
    end
    
    last_pc = txn.addr;
  endfunction
  
  // Check data read
  function void check_data_read(picorv32_mem_txn txn);
    num_data_reads++;
    
    `uvm_info("SCB", $sformatf("DATA RD [0x%08x] = 0x%08x", 
              txn.addr, txn.data), UVM_HIGH)
    
    // Check for reads from unmapped regions
    if (txn.addr >= 32'h10000000 && txn.addr < 32'h20000000) begin
      `uvm_info("SCB", $sformatf("I/O read from 0x%08x", txn.addr), UVM_MEDIUM)
    end
  endfunction
  
  // Check data write
  function void check_data_write(picorv32_mem_txn txn);
    num_data_writes++;
    
    `uvm_info("SCB", $sformatf("DATA WR [0x%08x] = 0x%08x (strb=%04b)", 
              txn.addr, txn.data, txn.wstrb), UVM_HIGH)
    
    // Check for writes to code region (potential self-modifying code)
    if (txn.addr < 32'h00010000) begin
      `uvm_warning("SCB", $sformatf("Write to code region: 0x%08x", txn.addr))
      num_warnings++;
    end
  endfunction
  
  // Check phase
  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    
    if (num_errors > 0) begin
      `uvm_error("SCB", $sformatf("Scoreboard detected %0d errors", num_errors))
    end
    
    if (num_instructions == 0) begin
      `uvm_error("SCB", "No instructions were executed!")
      num_errors++;
    end
  endfunction
  
  // Report phase
  function void report_phase(uvm_phase phase);
    string status;
    
    status = (num_errors == 0) ? "PASSED" : "FAILED";
    
    `uvm_info("SCB", $sformatf(
      "\n" +
      "╔══════════════════════════════════════════╗\n" +
      "║         SCOREBOARD SUMMARY               ║\n" +
      "╠══════════════════════════════════════════╣\n" +
      "║  Instructions executed: %6d           ║\n" +
      "║  Data reads:            %6d           ║\n" +
      "║  Data writes:           %6d           ║\n" +
      "║  Warnings:              %6d           ║\n" +
      "║  Errors:                %6d           ║\n" +
      "╠══════════════════════════════════════════╣\n" +
      "║  Status:                %s            ║\n" +
      "╚══════════════════════════════════════════╝",
      num_instructions, num_data_reads, num_data_writes, 
      num_warnings, num_errors, status), UVM_LOW)
  endfunction
  
endclass : picorv32_scoreboard
