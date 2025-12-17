// PicoRV32 Coverage Collector
//
// Functional coverage measures which design scenarios have been exercised
// during verification. Unlike code coverage (lines, branches), functional
// coverage is defined by the verification engineer to track design intent.
//
// COVERAGE-DRIVEN VERIFICATION (CDV):
// ┌─────────────────────────────────────────────────────────────┐
// │                                                             │
// │    Verification Plan ──▶ Covergroups ──▶ Coverage Goals    │
// │           │                   │                 │           │
// │           │                   ▼                 │           │
// │           │           ┌─────────────┐           │           │
// │           │           │   Sample    │           │           │
// │           │           │ Transactions│           │           │
// │           │           └──────┬──────┘           │           │
// │           │                  │                  │           │
// │           ▼                  ▼                  ▼           │
// │    ┌─────────────────────────────────────────────────┐     │
// │    │              Coverage Report                     │     │
// │    │  - Which instructions tested?                    │     │
// │    │  - Which register combinations used?             │     │
// │    │  - Which address ranges accessed?                │     │
// │    │  - Coverage holes = missing test scenarios       │     │
// │    └─────────────────────────────────────────────────┘     │
// │                                                             │
// └─────────────────────────────────────────────────────────────┘
//
// RISC-V COVERAGE MODEL:
//
// 1. INSTRUCTION COVERAGE
//    - All RV32I opcodes (LUI, AUIPC, JAL, JALR, branches, etc.)
//    - All RV32M extensions (MUL, DIV, REM)
//    - All RV32C compressed instructions
//
// 2. OPERAND COVERAGE
//    - Register usage (x0-x31 for rd, rs1, rs2)
//    - Immediate value ranges
//    - Special cases (x0 as destination, x0 as source)
//
// 3. CROSS COVERAGE
//    - Instruction sequences (e.g., load followed by use)
//    - Memory access patterns
//
// KEY UVM CONCEPTS:
//
// 1. uvm_subscriber BASE CLASS
//    - Simplified subscriber with built-in analysis_export
//    - Just implement write() function
//    - Automatically handles connection setup
//
// 2. COVERGROUPS
//    - SystemVerilog construct for functional coverage
//    - Coverpoints: individual items to track
//    - Bins: value ranges/categories to count
//    - Cross: combinations of coverpoints
//
// 3. SAMPLING
//    - covergroup.sample() captures current values
//    - Called when relevant transaction observed
//    - Filter with 'iff' clause for conditional sampling
//
// 4. COVERAGE REPORTING
//    - get_coverage() returns percentage
//    - Goal: typically 100% of specified bins
//    - Coverage holes indicate untested scenarios
//
//============================================================================

class picorv32_coverage extends uvm_subscriber #(picorv32_mem_txn);
  `uvm_component_utils(picorv32_coverage)
  
  // Transaction handle
  picorv32_mem_txn txn;
  
  // Decoded instruction fields
  logic [6:0]  opcode;
  logic [4:0]  rd, rs1, rs2;
  logic [2:0]  funct3;
  logic [6:0]  funct7;
  
  //==========================================================================
  // Instruction Opcode Coverage
  //==========================================================================
  covergroup instr_opcode_cg;
    option.per_instance = 1;
    option.name = "instr_opcode_cg";
    
    opcode_cp: coverpoint opcode {
      bins lui     = {7'b0110111};
      bins auipc   = {7'b0010111};
      bins jal     = {7'b1101111};
      bins jalr    = {7'b1100111};
      bins branch  = {7'b1100011};
      bins load    = {7'b0000011};
      bins store   = {7'b0100011};
      bins op_imm  = {7'b0010011};
      bins op      = {7'b0110011};
      bins fence   = {7'b0001111};
      bins system  = {7'b1110011};
      bins illegal = default;
    }
  endgroup
  
  //==========================================================================
  // Branch Instruction Coverage
  //==========================================================================
  covergroup branch_cg;
    option.per_instance = 1;
    option.name = "branch_cg";
    
    branch_type_cp: coverpoint funct3 iff (opcode == 7'b1100011) {
      bins beq  = {3'b000};
      bins bne  = {3'b001};
      bins blt  = {3'b100};
      bins bge  = {3'b101};
      bins bltu = {3'b110};
      bins bgeu = {3'b111};
    }
  endgroup
  
  //==========================================================================
  // Load/Store Coverage
  //==========================================================================
  covergroup loadstore_cg;
    option.per_instance = 1;
    option.name = "loadstore_cg";
    
    load_type_cp: coverpoint funct3 iff (opcode == 7'b0000011) {
      bins lb  = {3'b000};
      bins lh  = {3'b001};
      bins lw  = {3'b010};
      bins lbu = {3'b100};
      bins lhu = {3'b101};
    }
    
    store_type_cp: coverpoint funct3 iff (opcode == 7'b0100011) {
      bins sb = {3'b000};
      bins sh = {3'b001};
      bins sw = {3'b010};
    }
  endgroup
  
  //==========================================================================
  // ALU Operation Coverage
  //==========================================================================
  covergroup alu_cg;
    option.per_instance = 1;
    option.name = "alu_cg";
    
    // Register-Immediate operations
    op_imm_cp: coverpoint funct3 iff (opcode == 7'b0010011) {
      bins addi  = {3'b000};
      bins slti  = {3'b010};
      bins sltiu = {3'b011};
      bins xori  = {3'b100};
      bins ori   = {3'b110};
      bins andi  = {3'b111};
      bins slli  = {3'b001};
      bins srli_srai = {3'b101};
    }
    
    // Register-Register operations
    op_cp: coverpoint funct3 iff (opcode == 7'b0110011) {
      bins add_sub = {3'b000};
      bins sll     = {3'b001};
      bins slt     = {3'b010};
      bins sltu    = {3'b011};
      bins xor_op  = {3'b100};
      bins srl_sra = {3'b101};
      bins or_op   = {3'b110};
      bins and_op  = {3'b111};
    }
  endgroup
  
  //==========================================================================
  // Register Usage Coverage
  //==========================================================================
  covergroup reg_usage_cg;
    option.per_instance = 1;
    option.name = "reg_usage_cg";
    
    rd_cp: coverpoint rd {
      bins x0  = {0};
      bins x1_ra = {1};
      bins x2_sp = {2};
      bins x3_15 = {[3:15]};
      bins x16_31 = {[16:31]};
    }
    
    rs1_cp: coverpoint rs1 {
      bins x0  = {0};
      bins x1_ra = {1};
      bins x2_sp = {2};
      bins x3_15 = {[3:15]};
      bins x16_31 = {[16:31]};
    }
    
    rs2_cp: coverpoint rs2 {
      bins x0  = {0};
      bins x1_ra = {1};
      bins x2_sp = {2};
      bins x3_15 = {[3:15]};
      bins x16_31 = {[16:31]};
    }
  endgroup
  
  //==========================================================================
  // Address Coverage
  //==========================================================================
  covergroup addr_cg;
    option.per_instance = 1;
    option.name = "addr_cg";
    
    pc_range_cp: coverpoint txn.addr[31:16] iff (txn.is_instr) {
      bins low_mem  = {16'h0000};
      bins mid_mem  = {[16'h0001:16'h000F]};
      bins high_mem = {[16'h0010:16'hFFFF]};
    }
    
    data_addr_cp: coverpoint txn.addr[31:16] iff (!txn.is_instr) {
      bins stack_region = {[16'hFFF0:16'hFFFF]};
      bins data_region  = {[16'h0001:16'h00FF]};
      bins io_region    = {[16'h1000:16'h1FFF]};
    }
  endgroup
  
  //==========================================================================
  // Constructor
  //==========================================================================
  function new(string name, uvm_component parent);
    super.new(name, parent);
    instr_opcode_cg = new();
    branch_cg       = new();
    loadstore_cg    = new();
    alu_cg          = new();
    reg_usage_cg    = new();
    addr_cg         = new();
  endfunction
  
  //==========================================================================
  // Write function - called for each transaction
  //==========================================================================
  function void write(picorv32_mem_txn t);
    txn = t;
    
    // Only sample instruction fetches
    if (txn.is_instr) begin
      // Decode instruction fields
      opcode = txn.data[6:0];
      rd     = txn.data[11:7];
      funct3 = txn.data[14:12];
      rs1    = txn.data[19:15];
      rs2    = txn.data[24:20];
      funct7 = txn.data[31:25];
      
      // Sample covergroups
      instr_opcode_cg.sample();
      branch_cg.sample();
      loadstore_cg.sample();
      alu_cg.sample();
      reg_usage_cg.sample();
    end
    
    // Always sample address coverage
    addr_cg.sample();
  endfunction
  
  //==========================================================================
  // Report coverage
  //==========================================================================
  function void report_phase(uvm_phase phase);
    real total_cov;
    
    total_cov = (instr_opcode_cg.get_coverage() + 
                 branch_cg.get_coverage() + 
                 loadstore_cg.get_coverage() + 
                 alu_cg.get_coverage() +
                 reg_usage_cg.get_coverage() +
                 addr_cg.get_coverage()) / 6.0;
    
    `uvm_info("COV", $sformatf(
      "\n" +
      "╔══════════════════════════════════════════╗\n" +
      "║         COVERAGE SUMMARY                 ║\n" +
      "╠══════════════════════════════════════════╣\n" +
      "║  Instruction Opcode:    %6.2f%%          ║\n" +
      "║  Branch Types:          %6.2f%%          ║\n" +
      "║  Load/Store Types:      %6.2f%%          ║\n" +
      "║  ALU Operations:        %6.2f%%          ║\n" +
      "║  Register Usage:        %6.2f%%          ║\n" +
      "║  Address Ranges:        %6.2f%%          ║\n" +
      "╠══════════════════════════════════════════╣\n" +
      "║  TOTAL COVERAGE:        %6.2f%%          ║\n" +
      "╚══════════════════════════════════════════╝",
      instr_opcode_cg.get_coverage(),
      branch_cg.get_coverage(),
      loadstore_cg.get_coverage(),
      alu_cg.get_coverage(),
      reg_usage_cg.get_coverage(),
      addr_cg.get_coverage(),
      total_cov), UVM_LOW)
  endfunction
  
endclass : picorv32_coverage
