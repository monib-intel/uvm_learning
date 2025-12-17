// PicoRV32 Virtual Sequence
//
// Virtual sequences coordinate activity across multiple sequencers without
// directly generating transactions. They start sub-sequences on the
// appropriate sequencers for complex multi-interface scenarios.
//
// VIRTUAL SEQUENCE PATTERN:
// ┌─────────────────────────────────────────────────────────────┐
// │                  Virtual Sequence                           │
// │                                                             │
// │  // Handles to real sequencers (set by test)               │
// │  picorv32_mem_sequencer mem_sqr;                           │
// │  picorv32_irq_sequencer irq_sqr;                           │
// │                                                             │
// │  task body();                                               │
// │    fork                                                     │
// │      mem_seq.start(mem_sqr);  // Run on mem sequencer      │
// │      irq_seq.start(irq_sqr);  // Run on irq sequencer      │
// │    join                                                     │
// │  endtask                                                    │
// └─────────────────────────────────────────────────────────────┘
//
// KEY CONCEPTS:
//
// 1. SEQUENCER HANDLES
//    - Virtual sequence doesn't have a default sequencer
//    - Must be given handles to real sequencers
//    - Usually set via p_sequencer or config_db
//
// 2. PARALLEL/SEQUENTIAL CONTROL
//    - fork/join: Run sequences in parallel
//    - Sequential calls: Run one after another
//    - fork/join_any: Race between sequences
//
// 3. SYNCHRONIZATION
//    - Use events or semaphores for coordination
//    - Can wait for specific conditions before starting
//
//============================================================================

class picorv32_base_vseq extends uvm_sequence;
  `uvm_object_utils(picorv32_base_vseq)
  `uvm_declare_p_sequencer(picorv32_virtual_sequencer)
  
  function new(string name = "picorv32_base_vseq");
    super.new(name);
  endfunction
  
  // Convenience method to get memory sequencer
  function picorv32_mem_sequencer get_mem_sequencer();
    return p_sequencer.mem_sequencer;
  endfunction
  
  virtual task body();
    `uvm_info("VSEQ", "Base virtual sequence - override body()", UVM_LOW)
  endtask
  
endclass : picorv32_base_vseq


//=============================================================================
// Simple Test Virtual Sequence
//=============================================================================
class picorv32_simple_vseq extends picorv32_base_vseq;
  `uvm_object_utils(picorv32_simple_vseq)
  
  // Sub-sequences
  picorv32_mem_random_seq mem_seq;
  
  function new(string name = "picorv32_simple_vseq");
    super.new(name);
  endfunction
  
  virtual task body();
    `uvm_info("VSEQ", "Starting simple virtual sequence", UVM_MEDIUM)
    
    // Create and configure memory sequence
    mem_seq = picorv32_mem_random_seq::type_id::create("mem_seq");
    mem_seq.num_transactions = 20;
    
    // Start on memory sequencer
    mem_seq.start(get_mem_sequencer());
    
    `uvm_info("VSEQ", "Simple virtual sequence complete", UVM_MEDIUM)
  endtask
  
endclass : picorv32_simple_vseq


//=============================================================================
// Stress Test Virtual Sequence
//=============================================================================
class picorv32_stress_vseq extends picorv32_base_vseq;
  `uvm_object_utils(picorv32_stress_vseq)
  
  // Configuration
  int unsigned num_iterations = 5;
  
  function new(string name = "picorv32_stress_vseq");
    super.new(name);
  endfunction
  
  virtual task body();
    picorv32_mem_random_seq rand_seq;
    picorv32_mem_wr_rd_seq  wr_rd_seq;
    
    `uvm_info("VSEQ", $sformatf("Starting stress test with %0d iterations", 
              num_iterations), UVM_MEDIUM)
    
    for (int i = 0; i < num_iterations; i++) begin
      `uvm_info("VSEQ", $sformatf("=== Iteration %0d ===", i), UVM_MEDIUM)
      
      // Random sequence
      rand_seq = picorv32_mem_random_seq::type_id::create("rand_seq");
      rand_seq.num_transactions = 50;
      rand_seq.start(get_mem_sequencer());
      
      // Write-read sequence
      wr_rd_seq = picorv32_mem_wr_rd_seq::type_id::create("wr_rd_seq");
      wr_rd_seq.base_addr = 32'h1000_0000 + (i * 32'h1000);
      wr_rd_seq.num_locations = 20;
      wr_rd_seq.start(get_mem_sequencer());
    end
    
    `uvm_info("VSEQ", "Stress test complete", UVM_MEDIUM)
  endtask
  
endclass : picorv32_stress_vseq


//=============================================================================
// Virtual Sequencer - coordinates multiple sequencers
//=============================================================================
class picorv32_virtual_sequencer extends uvm_sequencer;
  `uvm_component_utils(picorv32_virtual_sequencer)
  
  // Handles to real sequencers
  picorv32_mem_sequencer mem_sequencer;
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  
endclass : picorv32_virtual_sequencer
