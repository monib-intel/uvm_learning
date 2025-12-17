// PicoRV32 Memory Transaction
//
// A UVM Transaction (uvm_sequence_item) represents an abstract unit of
// communication between testbench components. It encapsulates all the
// information about a single memory operation.
//
// TRANSACTION vs SIGNAL-LEVEL:
// ┌─────────────────────────────────────────────────────────────┐
// │ SIGNAL LEVEL (DUT Interface)                                │
// │   mem_valid, mem_ready, mem_addr[31:0], mem_wdata[31:0],   │
// │   mem_rdata[31:0], mem_wstrb[3:0], mem_instr               │
// └─────────────────────────────────────────────────────────────┘
//                          ▼
// ┌─────────────────────────────────────────────────────────────┐
// │ TRANSACTION LEVEL (Testbench)                               │
// │   picorv32_mem_txn {                                        │
// │     addr, data, is_write, is_instr, wstrb, timestamp        │
// │   }                                                         │
// └─────────────────────────────────────────────────────────────┘
//
// KEY UVM CONCEPTS:
//
// 1. uvm_sequence_item BASE CLASS
//    - Extends uvm_object with sequencer handshake capability
//    - Can be used with sequences and sequencer-driver flow
//    - Supports randomization (rand fields + constraints)
//
// 2. `uvm_object_utils MACRO
//    - Registers class with UVM factory
//    - Enables type_id::create() for factory construction
//    - Required for factory overrides and cloning
//
// 3. FIELD AUTOMATION (optional but helpful)
//    - convert2string(): Human-readable representation for debug
//    - do_compare(): Compare two transactions for equality
//    - do_copy(): Deep copy for cloning
//    - do_print(): Formatted printing (alternative to convert2string)
//
// 4. CONSTRAINTS
//    - Define legal values for randomized fields
//    - addr_align_c: Word alignment for instruction fetches
//    - wstrb_valid_c: Write strobe consistency with operation type
//
// 5. RANDOMIZATION (rand keyword)
//    - Fields marked 'rand' can be randomized with .randomize()
//    - Constraints control random value generation
//    - Enables constrained-random verification
//
//============================================================================

class picorv32_mem_txn extends uvm_sequence_item;
  `uvm_object_utils(picorv32_mem_txn)
  
  // Transaction fields
  rand logic [31:0] addr;
  rand logic [31:0] data;
  rand logic [ 3:0] wstrb;
  rand logic        is_write;
  logic             is_instr;
  
  // Timing
  time              timestamp;
  
  // Constraints
  constraint addr_align_c {
    // Word-aligned for instruction fetches
    is_instr -> (addr[1:0] == 2'b00);
  }
  
  constraint wstrb_valid_c {
    // Write strobe must be non-zero for writes
    is_write -> (wstrb != 4'b0000);
    !is_write -> (wstrb == 4'b0000);
  }
  
  // Constructor
  function new(string name = "picorv32_mem_txn");
    super.new(name);
  endfunction
  
  // Convert to string for debug
  function string convert2string();
    return $sformatf("%s addr=0x%08x data=0x%08x wstrb=%04b instr=%0b",
                     is_write ? "WR" : "RD", addr, data, wstrb, is_instr);
  endfunction
  
  // Compare two transactions
  function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    picorv32_mem_txn rhs_;
    if (!$cast(rhs_, rhs)) return 0;
    return (addr == rhs_.addr) && 
           (data == rhs_.data) && 
           (wstrb == rhs_.wstrb) &&
           (is_write == rhs_.is_write);
  endfunction
  
  // Copy
  function void do_copy(uvm_object rhs);
    picorv32_mem_txn rhs_;
    super.do_copy(rhs);
    $cast(rhs_, rhs);
    addr     = rhs_.addr;
    data     = rhs_.data;
    wstrb    = rhs_.wstrb;
    is_write = rhs_.is_write;
    is_instr = rhs_.is_instr;
  endfunction
  
endclass : picorv32_mem_txn
