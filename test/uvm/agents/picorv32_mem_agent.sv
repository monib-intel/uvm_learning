// PicoRV32 Memory Agent
//
// A UVM Agent encapsulates all components needed to interface with a single
// DUT interface. The agent provides a reusable, self-contained verification
// component that can be instantiated in any environment.
//
// AGENT STRUCTURE:
// ┌─────────────────────────────────────────────────────────────┐
// │                    picorv32_mem_agent                       │
// │                                                             │
// │  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐     │
// │  │  sequencer  │───▶│   driver    │───▶│    DUT      │     │
// │  │             │    │             │    │  (memory    │     │
// │  │ (stimulus   │    │ (converts   │    │   interface)│     │
// │  │  control)   │    │  txns to    │    │             │     │
// │  │             │    │  pin-level) │    │             │     │
// │  └─────────────┘    └─────────────┘    └──────┬──────┘     │
// │                                               │             │
// │                     ┌─────────────┐           │             │
// │                     │   monitor   │◀──────────┘             │
// │                     │ (observes   │                         │
// │                     │  bus, makes │──────▶ analysis_port    │
// │                     │  txns)      │       (to scoreboard)   │
// │                     └─────────────┘                         │
// └─────────────────────────────────────────────────────────────┘
//
// ACTIVE vs PASSIVE MODE:
//   - ACTIVE:  Has driver + sequencer + monitor (generates stimulus)
//   - PASSIVE: Has monitor only (observes existing traffic)
//
// KEY CONCEPTS:
//
// 1. SEQUENCER-DRIVER HANDSHAKE
//    - Sequencer provides transactions via seq_item_port
//    - Driver consumes via seq_item_port.get_next_item()
//    - Driver signals completion via seq_item_port.item_done()
//
// 2. MONITOR ANALYSIS PORT
//    - Monitor creates transaction objects from observed signals
//    - Broadcasts to all connected subscribers (scoreboard, coverage)
//    - Non-blocking: doesn't wait for subscribers
//
// 3. CONFIGURATION
//    - Agent configuration (active/passive) set via uvm_config_db
//    - Virtual interface handle obtained from config_db
//
//============================================================================

class picorv32_mem_agent extends uvm_agent;
  `uvm_component_utils(picorv32_mem_agent)
  
  // Components
  picorv32_mem_driver    driver;
  picorv32_mem_monitor   monitor;
  picorv32_mem_sequencer sequencer;
  
  // Analysis port (passthrough from monitor)
  uvm_analysis_port #(picorv32_mem_txn) analysis_port;
  
  // Constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  
  // Build phase
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Monitor always exists (passive or active)
    monitor = picorv32_mem_monitor::type_id::create("monitor", this);
    
    // Driver and sequencer only in active mode
    if (get_is_active() == UVM_ACTIVE) begin
      driver    = picorv32_mem_driver::type_id::create("driver", this);
      sequencer = picorv32_mem_sequencer::type_id::create("sequencer", this);
    end
    
    analysis_port = new("analysis_port", this);
  endfunction
  
  // Connect phase
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    // Connect monitor's analysis port to agent's port
    monitor.analysis_port.connect(analysis_port);
    
    // Connect driver to sequencer in active mode
    if (get_is_active() == UVM_ACTIVE) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
    end
  endfunction
  
endclass : picorv32_mem_agent
