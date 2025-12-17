// PicoRV32 Memory Sequencer
// Controls stimulus generation for memory interface

class picorv32_mem_sequencer extends uvm_sequencer #(picorv32_mem_txn);
  `uvm_component_utils(picorv32_mem_sequencer)
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  
endclass : picorv32_mem_sequencer
