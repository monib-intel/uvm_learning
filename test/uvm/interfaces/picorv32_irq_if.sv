// PicoRV32 IRQ Interface
// Connects UVM testbench to PicoRV32 interrupt signals

interface picorv32_irq_if(input logic clk, input logic resetn);
  
  // IRQ signals
  logic [31:0] irq;    // Interrupt request (input to CPU)
  logic [31:0] eoi;    // End of interrupt (output from CPU)
  
  // Clocking block for driver
  clocking driver_cb @(posedge clk);
    default input #1step output #1step;
    output irq;
    input  eoi;
  endclocking
  
  // Clocking block for monitor
  clocking monitor_cb @(posedge clk);
    default input #1step;
    input irq;
    input eoi;
  endclocking
  
  // Modports
  modport driver(clocking driver_cb, input clk, input resetn);
  modport monitor(clocking monitor_cb, input clk, input resetn);
  modport dut(input irq, output eoi);
  
endinterface : picorv32_irq_if
