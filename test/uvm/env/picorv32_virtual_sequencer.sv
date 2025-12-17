// PicoRV32 Virtual Sequencer
//
// A Virtual Sequencer is a UVM component that provides handles to multiple
// sequencers, enabling coordinated stimulus generation across interfaces.
// It does NOT derive from uvm_sequencer, but rather from uvm_component.
//
// VIRTUAL SEQUENCER CONCEPT:
// ┌────────────────────────────────────────────────────────────────────┐
// │                     Virtual Sequencer                              │
// │  ┌──────────────┐   ┌──────────────┐   ┌──────────────┐           │
// │  │ mem_seqr     │   │ irq_seqr     │   │ pcpi_seqr    │           │
// │  │ (handle)     │   │ (handle)     │   │ (handle)     │           │
// │  └──────────────┘   └──────────────┘   └──────────────┘           │
// └────────────────────────────────────────────────────────────────────┘
//                              │
//                   ┌──────────┴──────────┐
//                   │   Virtual Sequence  │
//                   │   (Coordinates)     │
//                   └─────────────────────┘
//
// WHY USE A VIRTUAL SEQUENCER:
//
// 1. MULTI-INTERFACE COORDINATION
//    - DUT often has multiple interfaces (memory, IRQ, AXI, etc.)
//    - Virtual sequences need access to all sequencers
//    - Virtual sequencer provides central access point
//
// 2. TEST SCENARIO ABSTRACTION
//    - Tests deal with one virtual sequencer
//    - Implementation details hidden
//    - Easy to add/remove agents
//
// 3. SYNCHRONIZATION
//    - Virtual sequences can coordinate timing
//    - Example: Assert IRQ, wait for memory write, deassert IRQ
//
// USAGE IN VIRTUAL SEQUENCES:
//    class my_vseq extends uvm_sequence;
//      `uvm_declare_p_sequencer(picorv32_virtual_sequencer)
//      
//      task body();
//        mem_seq.start(p_sequencer.mem_seqr);  // Access via handle
//      endtask
//    endclass
//
//============================================================================

class picorv32_virtual_sequencer extends uvm_sequencer;
  `uvm_component_utils(picorv32_virtual_sequencer)
  
  //--------------------------------------------------------------------------
  // Sequencer Handles
  //--------------------------------------------------------------------------
  // These handles are set in the environment's connect_phase.
  // Virtual sequences access real sequencers through these handles.
  //--------------------------------------------------------------------------
  
  // Memory interface sequencer handle
  picorv32_mem_sequencer mem_sequencer;
  
  // Future expansion: Add more sequencer handles as agents are added
  // picorv32_irq_sequencer irq_seqr;
  // picorv32_pcpi_sequencer pcpi_seqr;
  
  //--------------------------------------------------------------------------
  // Constructor
  //--------------------------------------------------------------------------
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  
  //--------------------------------------------------------------------------
  // Build Phase
  //--------------------------------------------------------------------------
  // Virtual sequencer doesn't create sequencers - just holds handles.
  // The actual sequencers are created in their respective agents.
  //--------------------------------------------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("VSEQR", "Building virtual sequencer", UVM_MEDIUM)
  endfunction
  
endclass : picorv32_virtual_sequencer
