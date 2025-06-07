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
  - [x] TSX (Transfer Stack Pointer to X)
  - [x] TXS (Transfer X to Stack Pointer)

- **Stack Operations**

  - [x] PHA (Push Accumulator)
  - [x] PHP (Push Processor Status)
  - [x] PLA (Pull Accumulator)
  - [x] PLP (Pull Processor Status)

- **Decrements & Increments**

  - [x] INX (Increment X Register)
  - [x] INY (Increment Y Register)
  - [x] INC (Increment Memory)
  - [x] DEX (Decrement X Register)
  - [x] DEY (Decrement Y Register)
  - [x] DEC (Decrement Memory)

- **Arithmetic Operations**

  - [x] ADC (Add with Carry)
  - [x] SBC (Subtract with Carry)
  - [x] CMP (Compare Accumulator)
  - [x] CPX (Compare X Register)
  - [x] CPY (Compare Y Register)

- **Logical Operations**

  - [x] AND (Logical AND)
  - [x] EOR (Exclusive OR)
  - [x] ORA (Logical OR)
  - [x] BIT (Bit Test)

- **Shifts & Rotates**

  - [x] ASL (Arithmetic Shift Left)
  - [x] LSR (Logical Shift Right)
  - [x] ROL (Rotate Left)
  - [x] ROR (Rotate Right)

- **Jumps & Calls**

  - [x] JMP (Jump)
  - [x] JSR (Jump to Subroutine)
  - [x] RTS (Return from Subroutine)
  - [x] RTI (Return from Interrupt)

- **Branches**

  - [x] BCC (Branch if Carry Clear)
  - [x] BCS (Branch if Carry Set)
  - [x] BEQ (Branch if Equal)
  - [x] BMI (Branch if Minus)
  - [x] BNE (Branch if Not Equal)
  - [x] BPL (Branch if Positive)
  - [x] BVC (Branch if Overflow Clear)
  - [x] BVS (Branch if Overflow Set)

- **Status Flag Changes**

  - [x] CLC (Clear Carry Flag)
  - [x] CLD (Clear Decimal Mode)
  - [x] CLI (Clear Interrupt Disable)
  - [x] CLV (Clear Overflow Flag)
  - [x] SEC (Set Carry Flag)
  - [x] SED (Set Decimal Flag)
  - [x] SEI (Set Interrupt Disable)

- **Other**
  - [x] BRK (Force Interrupt)
  - [x] NOP (No Operation)

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
