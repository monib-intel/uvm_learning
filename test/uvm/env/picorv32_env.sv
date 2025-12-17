// PicoRV32 UVM Environment
//
// The UVM Environment (uvm_env) is the top-level container that holds all
// verification components. It provides a reusable verification structure
// that can be instantiated in different tests.
//
// ENVIRONMENT RESPONSIBILITIES:
// ┌────────────────────────────────────────────────────────────┐
// │                    picorv32_env                            │
// │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │
// │  │  mem_agent   │  │  scoreboard  │  │   coverage   │     │
// │  │  (active)    │  │  (checker)   │  │  (metrics)   │     │
// │  └──────────────┘  └──────────────┘  └──────────────┘     │
// └────────────────────────────────────────────────────────────┘
//
// KEY CONCEPTS:
//
// 1. BUILD PHASE (build_phase)
//    - Components are created using factory: type_id::create()
//    - Factory enables runtime type substitution for flexibility
//    - Build order: top-down (parent before children)
//
// 2. CONNECT PHASE (connect_phase)  
//    - TLM (Transaction Level Modeling) connections established
//    - Analysis ports broadcast transactions to multiple subscribers
//    - Pattern: producer.port.connect(consumer.export)
//
// 3. ANALYSIS PORTS
//    - Monitor broadcasts observed transactions
//    - Scoreboard receives for checking
//    - Coverage receives for functional coverage sampling
//    - One-to-many connection (publish-subscribe pattern)
//
// EXTENDING THE ENVIRONMENT:
//    - Add more agents for additional interfaces (IRQ, PCPI)
//    - Add reference models for self-checking
//    - Override components using factory for different configurations
//
//============================================================================

class picorv32_env extends uvm_env;
  `uvm_component_utils(picorv32_env)
  
  // Agents
  picorv32_mem_agent mem_agent;
  
  // Virtual sequencer for coordinating multiple sequencers
  picorv32_virtual_sequencer virtual_sequencer;
  
  // Scoreboard
  picorv32_scoreboard scoreboard;
  
  // Coverage collector
  picorv32_coverage coverage;
  
  // Constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  
  // Build phase - create components
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    `uvm_info("ENV", "Building PicoRV32 environment", UVM_MEDIUM)
    
    // Create memory agent (active mode - it drives the memory interface)
    mem_agent = picorv32_mem_agent::type_id::create("mem_agent", this);
    
    // Create virtual sequencer
    virtual_sequencer = picorv32_virtual_sequencer::type_id::create("virtual_sequencer", this);
    
    // Create scoreboard
    scoreboard = picorv32_scoreboard::type_id::create("scoreboard", this);
    
    // Create coverage collector
    coverage = picorv32_coverage::type_id::create("coverage", this);
  endfunction
  
  // Connect phase - wire up components
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    `uvm_info("ENV", "Connecting PicoRV32 environment", UVM_MEDIUM)
    
    // Connect memory agent's monitor to scoreboard
    mem_agent.analysis_port.connect(scoreboard.mem_export);
    
    // Connect memory agent's monitor to coverage
    mem_agent.analysis_port.connect(coverage.analysis_export);
    
    // Connect virtual sequencer to agent sequencers
    virtual_sequencer.mem_sequencer = mem_agent.sequencer;
  endfunction
  
  // Report phase
  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info("ENV", "PicoRV32 environment report complete", UVM_MEDIUM)
  endfunction
  
endclass : picorv32_env
