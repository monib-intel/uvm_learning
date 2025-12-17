"""
PicoRV32 cocotb Testbench
=========================

cocotb is an open-source Python-based verification framework that provides
a modern alternative to traditional HDL testbenches. It integrates with
open-source simulators like Icarus Verilog and Verilator.

Usage:
    make cocotb-icarus
    make cocotb-verilator

Features demonstrated:
    - Coroutine-based test structure
    - Clock generation
    - Reset handling
    - Memory interface simulation
    - Transaction monitoring
    - Functional coverage (basic)
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, Timer, ClockCycles
from cocotb.result import TestFailure
from collections import defaultdict


class MemoryModel:
    """Simple memory model for PicoRV32"""
    
    def __init__(self, size=65536):
        self.memory = defaultdict(int)
        self.size = size
        
    def load_firmware(self, filename):
        """Load firmware from hex file"""
        addr = 0
        with open(filename, 'r') as f:
            for line in f:
                # Strip comments
                if '//' in line:
                    line = line[:line.index('//')]
                line = line.strip()
                if not line:
                    continue
                    
                # Handle address directive
                if line.startswith('@'):
                    addr = int(line[1:], 16)
                    continue
                    
                # Parse data
                if len(line) >= 8:
                    data = int(line[:8], 16)
                    self.memory[addr >> 2] = data
                    addr += 4
                    
        cocotb.log.info(f"Loaded firmware from {filename}")
        
    def read(self, addr):
        """Read 32-bit word"""
        return self.memory[addr >> 2]
        
    def write(self, addr, data, strb):
        """Write with byte strobes"""
        word_addr = addr >> 2
        current = self.memory[word_addr]
        
        if strb & 0x1:
            current = (current & 0xFFFFFF00) | (data & 0x000000FF)
        if strb & 0x2:
            current = (current & 0xFFFF00FF) | (data & 0x0000FF00)
        if strb & 0x4:
            current = (current & 0xFF00FFFF) | (data & 0x00FF0000)
        if strb & 0x8:
            current = (current & 0x00FFFFFF) | (data & 0xFF000000)
            
        self.memory[word_addr] = current


class CoverageCollector:
    """Basic functional coverage collector"""
    
    def __init__(self):
        self.instr_count = 0
        self.data_read_count = 0
        self.data_write_count = 0
        self.opcodes_seen = set()
        self.addr_regions = defaultdict(int)
        
    def sample_transaction(self, addr, data, is_write, is_instr):
        if is_instr:
            self.instr_count += 1
            # Extract opcode from instruction
            opcode = data & 0x7F
            self.opcodes_seen.add(opcode)
        elif is_write:
            self.data_write_count += 1
        else:
            self.data_read_count += 1
            
        # Track address regions
        region = (addr >> 16) & 0xFFFF
        self.addr_regions[region] += 1
        
    def report(self):
        cocotb.log.info("=" * 50)
        cocotb.log.info("       COVERAGE SUMMARY")
        cocotb.log.info("=" * 50)
        cocotb.log.info(f"  Instructions fetched: {self.instr_count}")
        cocotb.log.info(f"  Data reads:          {self.data_read_count}")
        cocotb.log.info(f"  Data writes:         {self.data_write_count}")
        cocotb.log.info(f"  Unique opcodes:      {len(self.opcodes_seen)}")
        cocotb.log.info(f"  Opcodes seen:        {[hex(o) for o in sorted(self.opcodes_seen)]}")
        cocotb.log.info("=" * 50)


class PicoRV32Driver:
    """Memory interface driver for PicoRV32"""
    
    def __init__(self, dut, memory, coverage):
        self.dut = dut
        self.memory = memory
        self.coverage = coverage
        self.cycle_count = 0
        
    async def run(self):
        """Main driver loop"""
        self.dut.mem_ready.value = 0
        self.dut.mem_rdata.value = 0
        self.dut.irq.value = 0
        
        while True:
            await RisingEdge(self.dut.clk)
            self.cycle_count += 1
            
            if self.dut.mem_valid.value == 1 and self.dut.mem_ready.value == 0:
                addr = int(self.dut.mem_addr.value)
                wstrb = int(self.dut.mem_wstrb.value)
                is_instr = int(self.dut.mem_instr.value)
                
                if wstrb != 0:
                    # Write
                    wdata = int(self.dut.mem_wdata.value)
                    self.memory.write(addr, wdata, wstrb)
                    cocotb.log.debug(f"[{self.cycle_count}] MEM WR [{addr:08x}] = {wdata:08x} (strb={wstrb:x})")
                    self.coverage.sample_transaction(addr, wdata, True, False)
                else:
                    # Read
                    rdata = self.memory.read(addr)
                    cocotb.log.debug(f"[{self.cycle_count}] MEM RD [{addr:08x}] = {rdata:08x} {'(instr)' if is_instr else '(data)'}")
                    self.coverage.sample_transaction(addr, rdata, False, is_instr)
                    
                self.dut.mem_rdata.value = self.memory.read(addr)
                self.dut.mem_ready.value = 1
            else:
                self.dut.mem_ready.value = 0


async def reset_dut(dut, cycles=10):
    """Reset the DUT"""
    dut.resetn.value = 0
    await ClockCycles(dut.clk, cycles)
    dut.resetn.value = 1
    cocotb.log.info("Reset released")


@cocotb.test()
async def test_simple_firmware(dut):
    """Run simple firmware and check for trap"""
    
    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())
    
    # Initialize
    memory = MemoryModel()
    coverage = CoverageCollector()
    driver = PicoRV32Driver(dut, memory, coverage)
    
    # Load firmware
    memory.load_firmware("firmware/simple_test.hex")
    
    # Reset
    await reset_dut(dut)
    
    # Start driver
    cocotb.start_soon(driver.run())
    
    # Wait for trap or timeout
    max_cycles = 10000
    for _ in range(max_cycles):
        await RisingEdge(dut.clk)
        if dut.trap.value == 1:
            cocotb.log.info(f"TRAP detected at cycle {driver.cycle_count}")
            break
    else:
        raise TestFailure(f"Timeout after {max_cycles} cycles")
    
    # Report coverage
    coverage.report()
    
    cocotb.log.info("Test PASSED")


@cocotb.test()
async def test_memory_interface(dut):
    """Test memory read/write transactions"""
    
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())
    
    memory = MemoryModel()
    coverage = CoverageCollector()
    driver = PicoRV32Driver(dut, memory, coverage)
    
    # Pre-load some test patterns
    for i in range(16):
        memory.memory[i] = 0x00000013  # NOP
    memory.memory[16] = 0x00100073  # EBREAK
    
    await reset_dut(dut)
    cocotb.start_soon(driver.run())
    
    # Wait for completion
    for _ in range(1000):
        await RisingEdge(dut.clk)
        if dut.trap.value == 1:
            break
    
    coverage.report()
    cocotb.log.info("Memory interface test PASSED")
