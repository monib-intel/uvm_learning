// PicoRV32 UVM Tests
//
// UVM Tests (uvm_test) are the top-level components that configure and
// control the verification environment. Each test represents a specific
// verification scenario.
//
// TEST HIERARCHY:
// ┌─────────────────────────────────────────────────────────────┐
// │                      uvm_test                               │
// │                         │                                   │
// │                         ▼                                   │
// │  ┌─────────────────────────────────────────────────────┐   │
// │  │              picorv32_base_test                      │   │
// │  │  - Creates environment                               │   │
// │  │  - Common configuration                              │   │
// │  │  - Base run_phase behavior                           │   │
// │  └───────────────────────┬─────────────────────────────┘   │
// │                          │                                  │
// │            ┌─────────────┼─────────────┐                    │
// │            ▼             ▼             ▼                    │
// │     ┌───────────┐ ┌───────────┐ ┌───────────┐              │
// │     │ simple    │ │ random    │ │ stress    │              │
// │     │ _test     │ │ _delay    │ │ _test     │              │
// │     │           │ │ _test     │ │           │              │
// │     └───────────┘ └───────────┘ └───────────┘              │
// └─────────────────────────────────────────────────────────────┘
//
// KEY UVM CONCEPTS:
//
// 1. TEST SELECTION
//    - Specified at runtime: +UVM_TESTNAME=picorv32_simple_test
//    - run_test() creates and runs the specified test
//    - Enables running different scenarios without recompilation
//
// 2. ENVIRONMENT CREATION
//    - Test creates and configures the environment in build_phase
//    - Can override component types using factory
//    - Sets configuration for child components
//
// 3. PHASE OBJECTIONS
//    - phase.raise_objection(): Prevents phase from ending
//    - phase.drop_objection(): Allows phase to end when all dropped
//    - Critical for controlling test duration
//
// 4. TEST INHERITANCE
//    - Base test provides common functionality
//    - Derived tests modify behavior for specific scenarios
//    - Override phases to customize test behavior
//
// 5. FACTORY OVERRIDES
//    - Replace default components with modified versions
//    - type_override: Replace all instances of a type
//    - instance_override: Replace specific instance
//
// EXAMPLE USAGE:
//   # Run simple test
//   ./simv +UVM_TESTNAME=picorv32_simple_test +firmware=test.hex
//
//   # Run with random delays and high verbosity
//   ./simv +UVM_TESTNAME=picorv32_random_delay_test +UVM_VERBOSITY=UVM_HIGH
//
//============================================================================

class picorv32_base_test extends uvm_test;
  `uvm_component_utils(picorv32_base_test)
  
  // Environment
  picorv32_env env;
  
  // Test configuration
  string firmware_file = "firmware.hex";
  int unsigned timeout_cycles = 100000;
  
  // Constructor
  function new(string name = "picorv32_base_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  // Build phase
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    `uvm_info("TEST", "Building PicoRV32 base test", UVM_LOW)
    
    // Create environment
    env = picorv32_env::type_id::create("env", this);
    
    // Get firmware file from command line if provided
    if ($value$plusargs("firmware=%s", firmware_file)) begin
      `uvm_info("TEST", $sformatf("Using firmware: %s", firmware_file), UVM_LOW)
    end
  endfunction
  
  // End of elaboration - print topology
  function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    `uvm_info("TEST", "Printing UVM topology:", UVM_LOW)
    uvm_top.print_topology();
  endfunction
  
  // Run phase
  task run_phase(uvm_phase phase);
    phase.raise_objection(this, "Starting test");
    
    `uvm_info("TEST", "=== Test started ===", UVM_LOW)
    
    // Load firmware into memory
    if (env.mem_agent.driver != null) begin
      env.mem_agent.driver.load_firmware(firmware_file);
    end
    
    // Wait for CPU to execute
    fork
      begin
        // Timeout watchdog
        repeat (timeout_cycles) @(posedge env.mem_agent.driver.vif.clk);
        `uvm_warning("TEST", "Test timeout reached")
      end
      begin
        // Wait for trap signal (test completion)
        wait (env.mem_agent.driver.vif.trap);
        `uvm_info("TEST", "CPU trap detected - test complete", UVM_LOW)
      end
    join_any
    disable fork;
    
    // Allow some drain time
    repeat (100) @(posedge env.mem_agent.driver.vif.clk);
    
    `uvm_info("TEST", "=== Test finished ===", UVM_LOW)
    
    phase.drop_objection(this, "Test complete");
  endtask
  
  // Report phase
  function void report_phase(uvm_phase phase);
    uvm_report_server rs;
    int unsigned error_count;
    
    super.report_phase(phase);
    
    rs = uvm_report_server::get_server();
    error_count = rs.get_severity_count(UVM_ERROR) + rs.get_severity_count(UVM_FATAL);
    
    `uvm_info("TEST", $sformatf(
      "\n" +
      "╔══════════════════════════════════════════╗\n" +
      "║           TEST RESULT                    ║\n" +
      "╠══════════════════════════════════════════╣\n" +
      "║  Test:   %-30s ║\n" +
      "║  Status: %-30s ║\n" +
      "╚══════════════════════════════════════════╝",
      get_name(),
      (error_count == 0) ? "PASSED" : "FAILED"), UVM_NONE)
  endfunction
  
endclass : picorv32_base_test


//=============================================================================
// Simple Test - runs firmware and checks for completion
//=============================================================================
class picorv32_simple_test extends picorv32_base_test;
  `uvm_component_utils(picorv32_simple_test)
  
  function new(string name = "picorv32_simple_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
endclass : picorv32_simple_test


//=============================================================================
// Random Delay Test - adds random memory delays
//=============================================================================
class picorv32_random_delay_test extends picorv32_base_test;
  `uvm_component_utils(picorv32_random_delay_test)
  
  function new(string name = "picorv32_random_delay_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Configuration will be applied after build
  endfunction
  
  function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    // Enable random delays in driver
    env.mem_agent.driver.enable_random_delay = 1;
    `uvm_info("TEST", "Random memory delays enabled", UVM_LOW)
  endfunction
  
endclass : picorv32_random_delay_test
