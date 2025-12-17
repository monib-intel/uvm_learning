// PicoRV32 Memory Driver
//
// The UVM Driver converts abstract transactions into pin-level signal
// activity on the DUT interface. For PicoRV32, this driver acts as a
// memory subsystem, responding to CPU memory read/write requests.
//
// DRIVER RESPONSIBILITIES:
//   1. Wait for CPU to assert mem_valid (memory request)
//   2. Handle read: Return data from internal memory model
//   3. Handle write: Store data to internal memory model
//   4. Assert mem_ready to complete the transaction
//
// PICORV32 MEMORY PROTOCOL:
// ┌─────┐     ┌─────────────────────────────────┐
// │     │     │ READ:  mem_valid=1, wstrb=0     │
// │ CPU │────▶│ WRITE: mem_valid=1, wstrb!=0   │
// │     │     │        mem_addr, mem_wdata      │
// └─────┘     └─────────────────────────────────┘
//                              │
//                              ▼
// ┌─────────┐  ┌─────────────────────────────────┐
// │ Memory  │◀─│ Response: mem_ready=1           │
// │ Driver  │  │           mem_rdata (for reads) │
// └─────────┘  └─────────────────────────────────┘
//
// TIMING DIAGRAM:
//          ┌───┐   ┌───┐   ┌───┐   ┌───┐   ┌───┐
//   clk    │   │   │   │   │   │   │   │   │   │
//          ┘   └───┘   └───┘   └───┘   └───┘   └───
//              ┌───────────────┐
//   mem_valid  │               │
//          ────┘               └───────────────────
//                          ┌───┐
//   mem_ready              │   │
//          ────────────────┘   └───────────────────
//                          ├───┤
//   mem_rdata              │DAT│  (valid when ready)
//          ────────────────┴───┴───────────────────
//
// KEY UVM CONCEPTS:
//
// 1. VIRTUAL INTERFACE
//    - Obtained from uvm_config_db in build_phase
//    - Provides access to DUT signals from class-based testbench
//
// 2. RUN_PHASE TASK
//    - Only time-consuming phase (uses simulation time)
//    - Forever loop handles continuous bus activity
//    - @(posedge clk) synchronizes to clock edges
//
// 3. MEMORY MODEL
//    - Simple associative array models memory
//    - Firmware loaded via $readmemh()
//    - Byte-enable (wstrb) support for partial writes
//
//============================================================================

class picorv32_mem_driver extends uvm_driver #(picorv32_mem_txn);
  `uvm_component_utils(picorv32_mem_driver)
  
  // Virtual interface
  virtual picorv32_mem_if vif;
  
  // Memory model
  logic [31:0] memory [0:65535];  // 256KB memory
  
  // Configuration
  int unsigned response_delay = 0;  // Cycles to delay response
  bit          enable_random_delay = 0;
  
  // Constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  
  // Build phase
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    if (!uvm_config_db#(virtual picorv32_mem_if)::get(this, "", "mem_vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not found for driver")
    
    // Initialize memory to zero
    foreach (memory[i]) memory[i] = 32'h0;
  endfunction
  
  // Load firmware from hex file
  function void load_firmware(string filename);
    $readmemh(filename, memory);
    `uvm_info("DRV", $sformatf("Loaded firmware from %s", filename), UVM_LOW)
  endfunction
  
  // Run phase - respond to memory requests
  task run_phase(uvm_phase phase);
    // Initialize outputs
    vif.mem_ready <= 0;
    vif.mem_rdata <= 32'h0;
    
    // Wait for reset
    @(posedge vif.resetn);
    `uvm_info("DRV", "Reset released, starting driver", UVM_MEDIUM)
    
    forever begin
      @(posedge vif.clk);
      
      if (vif.mem_valid && !vif.mem_ready) begin
        // Optional delay for more realistic timing
        if (enable_random_delay) begin
          repeat ($urandom_range(0, 3)) @(posedge vif.clk);
        end else if (response_delay > 0) begin
          repeat (response_delay) @(posedge vif.clk);
        end
        
        // Handle the memory request
        handle_memory_request();
      end else begin
        vif.mem_ready <= 0;
      end
    end
  endtask
  
  // Handle a single memory request
  task handle_memory_request();
    logic [31:0] addr_word;
    addr_word = vif.mem_addr[17:2];  // Word address
    
    if (vif.mem_wstrb != 4'b0000) begin
      // Write operation
      if (vif.mem_wstrb[0]) memory[addr_word][7:0]   = vif.mem_wdata[7:0];
      if (vif.mem_wstrb[1]) memory[addr_word][15:8]  = vif.mem_wdata[15:8];
      if (vif.mem_wstrb[2]) memory[addr_word][23:16] = vif.mem_wdata[23:16];
      if (vif.mem_wstrb[3]) memory[addr_word][31:24] = vif.mem_wdata[31:24];
      
      `uvm_info("DRV", $sformatf("MEM WR [0x%08x] = 0x%08x (strb=%04b)", 
                vif.mem_addr, vif.mem_wdata, vif.mem_wstrb), UVM_HIGH)
    end else begin
      // Read operation
      `uvm_info("DRV", $sformatf("MEM RD [0x%08x] = 0x%08x %s", 
                vif.mem_addr, memory[addr_word], 
                vif.mem_instr ? "(instr)" : "(data)"), UVM_HIGH)
    end
    
    // Respond
    vif.mem_rdata <= memory[addr_word];
    vif.mem_ready <= 1;
    
    @(posedge vif.clk);
    vif.mem_ready <= 0;
  endtask
  
endclass : picorv32_mem_driver
