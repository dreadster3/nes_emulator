# NES Emulator

[![Build Status](https://dreadster3.github.io/nes_emulator/badges/build-status.svg)](https://github.com/dreadster3/nes_emulator/actions)
[![Coverage](https://dreadster3.github.io/nes_emulator/badges/plastic.svg)](https://dreadster3.github.io/nes_emulator/)

Simple Rust NES emulator.

Initially developed by following the tutorial [nes_ebook](https://bugzmanov.github.io/nes_ebook/).

## Implementation Status

### CPU Instructions

- **Load/Store Operations**

  - [x] LDA (Load Accumulator)
  - [x] LDX (Load X Register)
  - [x] LDY (Load Y Register)
  - [x] STA (Store Accumulator)

- **Register Transfers**

  - [x] TAX (Transfer Accumulator to X)
  - [x] TAY (Transfer Accumulator to Y)
  - [x] TXA (Transfer X to Accumulator)
  - [x] TYA (Transfer Y to Accumulator)
  - [ ] TSX (Transfer Stack Pointer to X)
  - [ ] TXS (Transfer X to Stack Pointer)

- **Stack Operations**

  - [ ] PHA (Push Accumulator)
  - [ ] PHP (Push Processor Status)
  - [ ] PLA (Pull Accumulator)
  - [ ] PLP (Pull Processor Status)

- **Decrements & Increments**

  - [x] INX (Increment X Register)
  - [x] INY (Increment Y Register)
  - [x] INC (Increment Memory)
  - [x] DEX (Decrement X Register)
  - [ ] DEY (Decrement Y Register)
  - [ ] DEC (Decrement Memory)

- **Arithmetic Operations**

  - [x] ADC (Add with Carry)
  - [ ] SBC (Subtract with Carry)
  - [ ] CMP (Compare Accumulator)
  - [ ] CPX (Compare X Register)
  - [ ] CPY (Compare Y Register)

- **Logical Operations**

  - [x] AND (Logical AND)
  - [ ] EOR (Exclusive OR)
  - [ ] ORA (Logical OR)
  - [ ] BIT (Bit Test)

- **Shifts & Rotates**

  - [x] ASL (Arithmetic Shift Left)
  - [ ] LSR (Logical Shift Right)
  - [ ] ROL (Rotate Left)
  - [ ] ROR (Rotate Right)

- **Jumps & Calls**

  - [ ] JMP (Jump)
  - [ ] JSR (Jump to Subroutine)
  - [ ] RTS (Return from Subroutine)
  - [ ] RTI (Return from Interrupt)

- **Branches**

  - [ ] BCC (Branch if Carry Clear)
  - [ ] BCS (Branch if Carry Set)
  - [ ] BEQ (Branch if Equal)
  - [ ] BMI (Branch if Minus)
  - [ ] BNE (Branch if Not Equal)
  - [ ] BPL (Branch if Positive)
  - [ ] BVC (Branch if Overflow Clear)
  - [ ] BVS (Branch if Overflow Set)

- **Status Flag Changes**

  - [ ] CLC (Clear Carry Flag)
  - [ ] CLD (Clear Decimal Mode)
  - [ ] CLI (Clear Interrupt Disable)
  - [ ] CLV (Clear Overflow Flag)
  - [ ] SEC (Set Carry Flag)
  - [ ] SED (Set Decimal Flag)
  - [ ] SEI (Set Interrupt Disable)

- **Other**
  - [x] BRK (Force Interrupt)
  - [ ] NOP (No Operation)

### Other Components

- [ ] PPU (Picture Processing Unit)
- [ ] APU (Audio Processing Unit)
- [ ] Controller Input
- [ ] Memory Mapper Support
- [ ] Full ROM Loading
- [ ] Game Rendering

## Building and Running

```bash
cargo build
cargo run
```

## Testing

```bash
cargo test
```
