// Verilator C++ Testbench for PicoRV32
// Provides fast simulation with waveform generation
//
// Usage: make run-verilator FIRMWARE=firmware/simple_test.hex

#include <verilated.h>
#include <verilated_vcd_c.h>
#include "Vpicorv32.h"
#include <iostream>
#include <fstream>
#include <cstring>

// Memory size (256KB)
#define MEM_SIZE 65536

class PicoRV32Testbench {
public:
    Vpicorv32* dut;
    VerilatedVcdC* trace;
    uint32_t memory[MEM_SIZE];
    uint64_t sim_time;
    uint64_t cycle_count;
    bool trace_enabled;
    
    PicoRV32Testbench() {
        dut = new Vpicorv32;
        trace = nullptr;
        sim_time = 0;
        cycle_count = 0;
        trace_enabled = true;
        
        // Initialize memory
        memset(memory, 0, sizeof(memory));
    }
    
    ~PicoRV32Testbench() {
        if (trace) {
            trace->close();
            delete trace;
        }
        delete dut;
    }
    
    void enable_trace(const char* filename) {
        Verilated::traceEverOn(true);
        trace = new VerilatedVcdC;
        dut->trace(trace, 99);
        trace->open(filename);
        trace_enabled = true;
        std::cout << "Waveform trace enabled: " << filename << std::endl;
    }
    
    bool load_firmware(const char* filename) {
        std::ifstream file(filename);
        if (!file.is_open()) {
            std::cerr << "Error: Cannot open firmware file: " << filename << std::endl;
            return false;
        }
        
        std::string line;
        uint32_t addr = 0;
        
        while (std::getline(file, line)) {
            // Skip comments and empty lines
            size_t pos = line.find("//");
            if (pos != std::string::npos) {
                line = line.substr(0, pos);
            }
            
            // Trim whitespace
            size_t start = line.find_first_not_of(" \t");
            if (start == std::string::npos) continue;
            line = line.substr(start);
            
            // Check for address directive
            if (line[0] == '@') {
                addr = std::stoul(line.substr(1), nullptr, 16);
                continue;
            }
            
            // Parse hex data
            if (line.length() >= 8) {
                uint32_t data = std::stoul(line.substr(0, 8), nullptr, 16);
                if (addr/4 < MEM_SIZE) {
                    memory[addr/4] = data;
                    addr += 4;
                }
            }
        }
        
        std::cout << "Loaded firmware: " << filename << std::endl;
        return true;
    }
    
    void tick() {
        // Falling edge
        dut->clk = 0;
        dut->eval();
        if (trace) trace->dump(sim_time++);
        
        // Rising edge
        dut->clk = 1;
        dut->eval();
        if (trace) trace->dump(sim_time++);
        
        cycle_count++;
    }
    
    void reset(int cycles = 10) {
        dut->resetn = 0;
        for (int i = 0; i < cycles; i++) {
            tick();
        }
        dut->resetn = 1;
        std::cout << "Reset released at cycle " << cycle_count << std::endl;
    }
    
    void handle_memory() {
        if (dut->mem_valid && !dut->mem_ready) {
            uint32_t addr_word = (dut->mem_addr >> 2) & 0xFFFF;
            
            if (dut->mem_wstrb != 0) {
                // Write operation
                uint32_t data = memory[addr_word];
                if (dut->mem_wstrb & 1) data = (data & 0xFFFFFF00) | (dut->mem_wdata & 0x000000FF);
                if (dut->mem_wstrb & 2) data = (data & 0xFFFF00FF) | (dut->mem_wdata & 0x0000FF00);
                if (dut->mem_wstrb & 4) data = (data & 0xFF00FFFF) | (dut->mem_wdata & 0x00FF0000);
                if (dut->mem_wstrb & 8) data = (data & 0x00FFFFFF) | (dut->mem_wdata & 0xFF000000);
                memory[addr_word] = data;
                
                printf("[%lu] MEM WR [%08x] = %08x (strb=%x)\n", 
                       cycle_count, dut->mem_addr, dut->mem_wdata, dut->mem_wstrb);
            } else {
                // Read operation
                printf("[%lu] MEM RD [%08x] = %08x %s\n", 
                       cycle_count, dut->mem_addr, memory[addr_word],
                       dut->mem_instr ? "(instr)" : "(data)");
            }
            
            dut->mem_rdata = memory[addr_word];
            dut->mem_ready = 1;
        } else {
            dut->mem_ready = 0;
        }
    }
    
    int run(uint64_t max_cycles = 100000) {
        std::cout << "Starting simulation (max " << max_cycles << " cycles)..." << std::endl;
        
        // Initialize inputs
        dut->irq = 0;
        dut->pcpi_wr = 0;
        dut->pcpi_rd = 0;
        dut->pcpi_wait = 0;
        dut->pcpi_ready = 0;
        dut->mem_ready = 0;
        dut->mem_rdata = 0;
        
        reset();
        
        while (cycle_count < max_cycles) {
            handle_memory();
            tick();
            
            if (dut->trap) {
                std::cout << std::endl;
                std::cout << "========================================" << std::endl;
                std::cout << "  TRAP detected at cycle " << cycle_count << std::endl;
                std::cout << "  Simulation complete" << std::endl;
                std::cout << "========================================" << std::endl;
                return 0;
            }
        }
        
        std::cout << std::endl;
        std::cout << "========================================" << std::endl;
        std::cout << "  TIMEOUT after " << cycle_count << " cycles" << std::endl;
        std::cout << "========================================" << std::endl;
        return 1;
    }
};

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    
    PicoRV32Testbench tb;
    
    // Enable waveform tracing
    tb.enable_trace("picorv32_tb.vcd");
    
    // Load firmware from command line
    const char* firmware = "firmware/simple_test.hex";
    for (int i = 1; i < argc; i++) {
        if (strncmp(argv[i], "+firmware=", 10) == 0) {
            firmware = argv[i] + 10;
        }
    }
    
    if (!tb.load_firmware(firmware)) {
        return 1;
    }
    
    return tb.run();
}
