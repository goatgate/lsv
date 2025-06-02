# Buggy SystemVerilog Circuits Collection

This repository contains a collection of SystemVerilog circuits with intentionally introduced bugs for learning purposes. The circuits are organized into different categories to help practice testing, debugging, and verification skills.

## Project Structure

```
├── combinatorial/
│   ├── alu.sv           (Buggy ALU with incorrect operations)
│   ├── decoder.sv       (4-to-16 decoder with timing issues)
│   └── mux.sv           (8:1 multiplexer with incorrect selection)
├── sequential/
│   ├── counter.sv       (Up-down counter with reset issues)
│   ├── shift_reg.sv     (Shift register with data corruption)
│   └── fifo.sv          (FIFO with overflow problems)
├── fsm/
│   ├── traffic_light.sv (Traffic light controller with deadlock)
│   ├── vending.sv       (Vending machine with incorrect state transitions)
│   └── uart.sv          (UART controller with protocol violations)
├── multiplier/
│   ├── array_mult.sv    (Array multiplier with partial product errors)
│   ├── booth_mult.sv    (Booth multiplier with encoding issues)
│   └── wallace_mult.sv  (Wallace tree multiplier with carry propagation bugs)
└── testbenches/
    └── [corresponding testbenches for each module]

## Bug Categories

1. Combinatorial Circuits:
   - Incorrect boolean equations
   - Timing violations
   - Incomplete case statements
   - Priority encoder issues

2. Sequential Circuits:
   - Reset conditions
   - Clock domain crossing
   - Race conditions
   - Setup/Hold violations

3. Finite State Machines:
   - Unreachable states
   - Deadlock conditions
   - Missing state transitions
   - Incorrect output logic

4. Multipliers:
   - Sign extension errors
   - Partial product generation issues
   - Carry propagation problems
   - Timing path violations

## How to Use

1. Try to identify the bugs in each circuit
2. Write testbenches to detect the issues
3. Use assertions to catch the bugs
4. Fix the problems and verify the solutions

Each module contains comments indicating the intended functionality 
