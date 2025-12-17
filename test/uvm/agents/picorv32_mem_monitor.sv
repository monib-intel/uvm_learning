// PicoRV32 Memory Monitor
//
// The UVM Monitor observes DUT interface activity without affecting it
// (passive observation). It converts pin-level signals into transaction
// objects and broadcasts them via an analysis port.
//
// MONITOR RESPONSIBILITIES:
//   1. Observe memory interface signals (passive, non-intrusive)
//   2. Detect completed transactions (mem_valid && mem_ready)
//   3. Create transaction objects capturing observed data
//   4. Broadcast transactions to all connected subscribers
//
// ANALYSIS PORT PATTERN:
// ┌───────────────────────────────────────────────────────────┐
// │                      Monitor                              │
// │  ┌─────────────┐      ┌──────────────────────────────┐   │
// │  │ Observe     │      │      analysis_port           │   │
// │  │ Interface   │─────▶│  (uvm_analysis_port)         │   │
// │  │ Signals     │      │                              │   │
// │  └─────────────┘      └──────────────┬───────────────┘   │
// └──────────────────────────────────────│───────────────────┘
//                                        │
//               ┌────────────────────────┼────────────────────┐
//               │                        │                    │
//               ▼                        ▼                    ▼
//        ┌─────────────┐         ┌─────────────┐      ┌─────────────┐
//        │ Scoreboard  │         │  Coverage   │      │   Logger    │
//        │ (checking)  │         │  (metrics)  │      │  (debug)    │
//        └─────────────┘         └─────────────┘      └─────────────┘
//
// KEY UVM CONCEPTS:
//
// 1. ANALYSIS PORT (uvm_analysis_port)
//    - Implements publish-subscribe pattern
//    - One producer, multiple consumers
//    - Non-blocking write() - doesn't wait for subscribers
//    - Consumers implement uvm_analysis_imp or uvm_subscriber
//
// 2. TRANSACTION CREATION
//    - Use factory: type_id::create() for flexibility
//    - Capture all relevant signal values
//    - Include timestamp for timing analysis
//
// 3. PASSIVE MONITORING
//    - Monitor should NEVER drive signals
//    - Same monitor works in active or passive agent
//    - Enables protocol checking regardless of stimulus source
//
// 4. STATISTICS COLLECTION
//    - Track transaction counts by type
//    - Report in report_phase for test summary
//
//============================================================================

class picorv32_mem_monitor extends uvm_monitor;
  `uvm_component_utils(picorv32_mem_monitor)
  
  // Virtual interface
  virtual picorv32_mem_if vif;
  
  // Analysis port to broadcast transactions
  uvm_analysis_port #(picorv32_mem_txn) analysis_port;
  
  // Statistics
  int unsigned num_reads;
  int unsigned num_writes;
  int unsigned num_instr_fetches;
  
  // Constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
    analysis_port = new("analysis_port", this);
  endfunction
  
  // Build phase - get virtual interface
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual picorv32_mem_if)::get(this, "", "mem_vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not found for monitor")
  endfunction
  
  // Run phase - monitor bus activity
  task run_phase(uvm_phase phase);
    picorv32_mem_txn txn;
    
    // Wait for reset
    @(posedge vif.resetn);
    `uvm_info("MON", "Reset released, starting monitor", UVM_MEDIUM)
    
    forever begin
      @(posedge vif.clk);
      
      // Check for completed transaction
      if (vif.mem_valid && vif.mem_ready) begin
        txn = picorv32_mem_txn::type_id::create("txn");
        
        txn.addr      = vif.mem_addr;
        txn.wstrb     = vif.mem_wstrb;
        txn.is_write  = (vif.mem_wstrb != 4'b0000);
        txn.is_instr  = vif.mem_instr;
        txn.timestamp = $time;
        
        if (txn.is_write) begin
          txn.data = vif.mem_wdata;
          num_writes++;
        end else begin
          txn.data = vif.mem_rdata;
          if (txn.is_instr)
            num_instr_fetches++;
          else
            num_reads++;
        end
        
        // Broadcast transaction
        analysis_port.write(txn);
        
        `uvm_info("MON", txn.convert2string(), UVM_HIGH)
      end
      
      // Check for trap
      if (vif.trap) begin
        `uvm_warning("MON", "CPU trap detected!")
      end
    end
  endtask
  
  // Report phase - print statistics
  function void report_phase(uvm_phase phase);
    `uvm_info("MON", $sformatf(
      "\n========== Monitor Statistics ==========\n" +
      "  Instruction fetches: %0d\n" +
      "  Data reads:          %0d\n" +
      "  Data writes:         %0d\n" +
      "  Total transactions:  %0d\n" +
      "=========================================",
      num_instr_fetches, num_reads, num_writes,
      num_instr_fetches + num_reads + num_writes), UVM_LOW)
  endfunction
  
endclass : picorv32_mem_monitor
