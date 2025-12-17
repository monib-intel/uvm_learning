// PicoRV32 Memory Sequences
//
// UVM Sequences generate stimulus by creating transactions and sending them
// to drivers through sequencers. Sequences provide layered stimulus control:
//
// SEQUENCE HIERARCHY:
// ┌─────────────────────────────────────────────────────────────┐
// │                    Test                                     │
// │                      │                                      │
// │                      ▼                                      │
// │  ┌─────────────────────────────────────────────────────┐   │
// │  │              Virtual Sequence                        │   │
// │  │  (coordinates multiple sequencers)                   │   │
// │  └───────────────────────┬─────────────────────────────┘   │
// │                          │                                  │
// │            ┌─────────────┴─────────────┐                    │
// │            ▼                           ▼                    │
// │     ┌───────────┐               ┌───────────┐              │
// │     │ Mem Seq   │               │ IRQ Seq   │              │
// │     └─────┬─────┘               └─────┬─────┘              │
// │           │                           │                     │
// │           ▼                           ▼                     │
// │     ┌───────────┐               ┌───────────┐              │
// │     │ Sequencer │               │ Sequencer │              │
// │     └─────┬─────┘               └─────┬─────┘              │
// │           │                           │                     │
// │           ▼                           ▼                     │
// │     ┌───────────┐               ┌───────────┐              │
// │     │  Driver   │               │  Driver   │              │
// │     └───────────┘               └───────────┘              │
// └─────────────────────────────────────────────────────────────┘
//
// KEY CONCEPTS:
//
// 1. SEQUENCE BODY
//    - body() task generates transactions
//    - Use `uvm_do, `uvm_do_with macros for simplicity
//    - Or use start_item()/finish_item() for control
//
// 2. SEQUENCE MACROS
//    - `uvm_do(item): Create, randomize, send
//    - `uvm_do_with(item, {constraints}): With inline constraints
//    - `uvm_create(item): Just create
//    - `uvm_send(item): Just send
//
// 3. SEQUENCER-DRIVER HANDSHAKE
//    - start_item(): Request grant from sequencer
//    - finish_item(): Send to driver, wait for completion
//    - Driver calls get_next_item()/item_done()
//
//============================================================================

//=============================================================================
// Base Memory Sequence
//=============================================================================
class picorv32_mem_base_seq extends uvm_sequence #(picorv32_mem_txn);
  `uvm_object_utils(picorv32_mem_base_seq)
  
  function new(string name = "picorv32_mem_base_seq");
    super.new(name);
  endfunction
  
  // Override in derived sequences
  virtual task body();
    `uvm_info("SEQ", "Base sequence - override body() in derived class", UVM_LOW)
  endtask
  
endclass : picorv32_mem_base_seq


//=============================================================================
// Random Memory Sequence - generates random read/write transactions
//=============================================================================
class picorv32_mem_random_seq extends picorv32_mem_base_seq;
  `uvm_object_utils(picorv32_mem_random_seq)
  
  // Configuration
  rand int unsigned num_transactions;
  
  constraint num_txn_c {
    num_transactions inside {[10:100]};
  }
  
  function new(string name = "picorv32_mem_random_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    picorv32_mem_txn txn;
    
    `uvm_info("SEQ", $sformatf("Starting random sequence with %0d transactions", 
              num_transactions), UVM_MEDIUM)
    
    repeat (num_transactions) begin
      txn = picorv32_mem_txn::type_id::create("txn");
      
      start_item(txn);
      if (!txn.randomize()) begin
        `uvm_error("SEQ", "Randomization failed")
      end
      finish_item(txn);
      
      `uvm_info("SEQ", $sformatf("Sent: %s", txn.convert2string()), UVM_HIGH)
    end
    
    `uvm_info("SEQ", "Random sequence complete", UVM_MEDIUM)
  endtask
  
endclass : picorv32_mem_random_seq


//=============================================================================
// Write-Read Sequence - writes data then reads it back
//=============================================================================
class picorv32_mem_wr_rd_seq extends picorv32_mem_base_seq;
  `uvm_object_utils(picorv32_mem_wr_rd_seq)
  
  // Configuration
  logic [31:0] base_addr = 32'h1000_0000;
  int unsigned num_locations = 10;
  
  function new(string name = "picorv32_mem_wr_rd_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    picorv32_mem_txn wr_txn, rd_txn;
    logic [31:0] expected_data[$];
    
    `uvm_info("SEQ", $sformatf("Write-Read sequence: %0d locations starting at 0x%08x",
              num_locations, base_addr), UVM_MEDIUM)
    
    // Write phase
    for (int i = 0; i < num_locations; i++) begin
      wr_txn = picorv32_mem_txn::type_id::create("wr_txn");
      
      start_item(wr_txn);
      wr_txn.addr = base_addr + (i * 4);
      wr_txn.data = $urandom();
      wr_txn.is_write = 1;
      wr_txn.wstrb = 4'b1111;
      wr_txn.is_instr = 0;
      finish_item(wr_txn);
      
      expected_data.push_back(wr_txn.data);
      `uvm_info("SEQ", $sformatf("Write[%0d]: addr=0x%08x data=0x%08x", 
                i, wr_txn.addr, wr_txn.data), UVM_HIGH)
    end
    
    // Read phase
    for (int i = 0; i < num_locations; i++) begin
      rd_txn = picorv32_mem_txn::type_id::create("rd_txn");
      
      start_item(rd_txn);
      rd_txn.addr = base_addr + (i * 4);
      rd_txn.is_write = 0;
      rd_txn.wstrb = 4'b0000;
      rd_txn.is_instr = 0;
      finish_item(rd_txn);
      
      `uvm_info("SEQ", $sformatf("Read[%0d]: addr=0x%08x data=0x%08x (expected=0x%08x)", 
                i, rd_txn.addr, rd_txn.data, expected_data[i]), UVM_HIGH)
    end
    
    `uvm_info("SEQ", "Write-Read sequence complete", UVM_MEDIUM)
  endtask
  
endclass : picorv32_mem_wr_rd_seq


//=============================================================================
// Firmware Load Sequence - initializes memory with firmware
//=============================================================================
class picorv32_firmware_load_seq extends picorv32_mem_base_seq;
  `uvm_object_utils(picorv32_firmware_load_seq)
  
  // Firmware data (set by test)
  logic [31:0] firmware[$];
  logic [31:0] start_addr = 32'h0000_0000;
  
  function new(string name = "picorv32_firmware_load_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    picorv32_mem_txn txn;
    
    `uvm_info("SEQ", $sformatf("Loading %0d words of firmware at 0x%08x",
              firmware.size(), start_addr), UVM_MEDIUM)
    
    foreach (firmware[i]) begin
      txn = picorv32_mem_txn::type_id::create("txn");
      
      start_item(txn);
      txn.addr = start_addr + (i * 4);
      txn.data = firmware[i];
      txn.is_write = 1;
      txn.wstrb = 4'b1111;
      txn.is_instr = 0;
      finish_item(txn);
    end
    
    `uvm_info("SEQ", "Firmware load complete", UVM_MEDIUM)
  endtask
  
endclass : picorv32_firmware_load_seq
