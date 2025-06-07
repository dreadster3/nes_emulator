mod bus;
mod instructions;
pub mod memory;

use bitflags::bitflags;
use bus::Bus;
use derivative::Derivative;
use thiserror::Error;

use crate::opcodes::{AddressMode, Mnemonic, OPCODE_MAP};

use instructions::*;
use memory::Memory;

bitflags! {
    #[derive(Debug, Default, Eq, PartialEq)]
    pub struct Status: u8 {
        const Carry = 0b0000_0001;
        const Zero = 0b0000_0010;
        const InterruptDisable = 0b0000_0100;
        const Decimal = 0b0000_1000;
        const Break = 0b0001_0000;
        const Overflow = 0b0100_0000;
        const Negative = 0b1000_0000;
    }
}

const STACK_BASE: u16 = 0x0100;

#[derive(Derivative)]
#[derivative(Debug, Default)]
pub struct CPU {
    register_a: u8,
    register_x: u8,
    register_y: u8,
    pub status: Status,
    pub program_counter: u16,
    #[derivative(Default(value = "0xFF"))]
    stack_pointer: u8,
    bus: Bus,
}

#[derive(Error, Debug)]
pub enum CPUError {
    #[error("Unknown instruction 0x{0:02x}")]
    UnknownOpcode(u8),

    #[error("IO Error")]
    IOError(#[from] std::io::Error),
}

impl CPU {
    pub fn new(bus: Option<Bus>) -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: Status::empty(),
            program_counter: 0,
            stack_pointer: 0xFF,
            bus: bus.unwrap_or(Bus::new()),
        }
    }

    fn read_u8(&mut self) -> u8 {
        let result = self.mem_read_u8(self.program_counter);
        self.program_counter += 1;

        result
    }

    fn read_u16(&mut self) -> u16 {
        let lo = self.read_u8();
        let hi = self.read_u8();

        u16::from_le_bytes([lo, hi])
    }

    pub fn stack_push(&mut self, value: u8) {
        self.mem_write_u8(STACK_BASE + self.stack_pointer as u16, value);
        self.stack_pointer = self.stack_pointer.wrapping_sub(1);
    }

    pub fn stack_push_u16(&mut self, value: u16) {
        let bytes = value.to_be_bytes();
        self.stack_push(bytes[0]);
        self.stack_push(bytes[1]);
    }

    pub fn stack_pop(&mut self) -> u8 {
        self.stack_pointer = self.stack_pointer.wrapping_add(1);
        self.mem_read_u8(STACK_BASE + self.stack_pointer as u16)
    }

    pub fn stack_pop_u16(&mut self) -> u16 {
        let lo = self.stack_pop();
        let hi = self.stack_pop();

        u16::from_le_bytes([lo, hi])
    }

    pub fn set_stack_pointer(&mut self, value: u8) {
        self.stack_pointer = value;
        self.update_zero_and_negative_flags(self.stack_pointer);
    }

    pub fn get_stack_pointer(&self) -> u8 {
        self.stack_pointer
    }

    pub fn get_register_a(&self) -> u8 {
        self.register_a
    }

    pub fn get_register_x(&self) -> u8 {
        self.register_x
    }

    pub fn get_register_y(&self) -> u8 {
        self.register_y
    }

    pub fn set_register_a(&mut self, value: u8) {
        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    pub fn set_register_x(&mut self, value: u8) {
        self.register_x = value;
        self.update_zero_and_negative_flags(self.register_x);
    }

    pub fn set_register_y(&mut self, value: u8) {
        self.register_y = value;
        self.update_zero_and_negative_flags(self.register_y);
    }

    pub fn run(&mut self) -> Result<(), CPUError> {
        self.run_with_callback(|_| {})
    }

    pub fn run_with_callback<F>(&mut self, mut callback: F) -> Result<(), CPUError>
    where
        F: FnMut(&mut CPU),
    {
        loop {
            callback(self);

            let instruction = self.read_u8();
            let opcode = OPCODE_MAP
                .get(&instruction)
                .ok_or(CPUError::UnknownOpcode(instruction))?;

            let program_counter = self.program_counter;

            match opcode.mnemonic {
                Mnemonic::LDA => self.lda(&opcode.mode),
                Mnemonic::LDX => self.ldx(&opcode.mode),
                Mnemonic::LDY => self.ldy(&opcode.mode),
                Mnemonic::STA => self.sta(&opcode.mode),
                Mnemonic::AND => self.and(&opcode.mode),
                Mnemonic::EOR => self.eor(&opcode.mode),
                Mnemonic::ORA => self.ora(&opcode.mode),
                Mnemonic::ADC => self.adc(&opcode.mode),
                Mnemonic::SBC => self.sbc(&opcode.mode),
                Mnemonic::CMP => self.cmp(&opcode.mode),
                Mnemonic::CPX => self.cpx(&opcode.mode),
                Mnemonic::CPY => self.cpy(&opcode.mode),
                Mnemonic::ASL => self.asl(&opcode.mode),
                Mnemonic::LSR => self.lsr(&opcode.mode),
                Mnemonic::ROL => self.rol(&opcode.mode),
                Mnemonic::ROR => self.ror(&opcode.mode),
                Mnemonic::TAX => self.tax(),
                Mnemonic::TAY => self.tay(),
                Mnemonic::TXA => self.txa(),
                Mnemonic::TYA => self.tya(),
                Mnemonic::TXS => self.txs(),
                Mnemonic::TSX => self.tsx(),
                Mnemonic::INX => self.inx(),
                Mnemonic::INY => self.iny(),
                Mnemonic::INC => self.inc(&opcode.mode),
                Mnemonic::DEX => self.dex(),
                Mnemonic::DEY => self.dey(),
                Mnemonic::DEC => self.dec(&opcode.mode),
                Mnemonic::PHA => self.pha(),
                Mnemonic::PLA => self.pla(),
                Mnemonic::PHP => self.php(),
                Mnemonic::PLP => self.plp(),
                Mnemonic::JSR => self.jsr(&opcode.mode),
                Mnemonic::JMP => self.jmp(&opcode.mode),
                Mnemonic::RTS => self.rts(),
                Mnemonic::RTI => self.rti(),
                Mnemonic::CLI => self.cli(),
                Mnemonic::CLC => self.clc(),
                Mnemonic::CLD => self.cld(),
                Mnemonic::CLV => self.clv(),
                Mnemonic::SEC => self.sec(),
                Mnemonic::SEI => self.sei(),
                Mnemonic::SED => self.sed(),
                Mnemonic::BCC => self.bcc(),
                Mnemonic::BCS => self.bcs(),
                Mnemonic::BEQ => self.beq(),
                Mnemonic::BMI => self.bmi(),
                Mnemonic::BNE => self.bne(),
                Mnemonic::BPL => self.bpl(),
                Mnemonic::BVC => self.bvc(),
                Mnemonic::BVS => self.bvs(),
                Mnemonic::BIT => self.bit(&opcode.mode),
                Mnemonic::NOP => continue,
                Mnemonic::BRK => break,
            }

            if program_counter == self.program_counter {
                self.program_counter += (opcode.len - 1) as u16;
            }
        }

        Ok(())
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) -> Result<(), CPUError> {
        self.load(program);
        self.reset();
        self.run()
    }

    pub fn load(&mut self, program: Vec<u8>) {
        let start = 0x0600;
        for i in 0..(program.len() as u16) {
            self.mem_write_u8(i, program[i as usize]);
        }
        self.mem_write_u16(0xFFFC, start as u16);
    }

    pub fn reset(&mut self) {
        self.register_x = 0;
        self.register_a = 0;
        self.program_counter = 0;
        self.stack_pointer = 0xFF;
        self.status = Status::InterruptDisable;

        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    fn update_zero_flag(&mut self, result: u8) {
        if result == 0 {
            self.status.insert(Status::Zero);
        } else {
            self.status.remove(Status::Zero);
        }
    }

    fn update_negative_flag(&mut self, result: u8) {
        if result & 0x80 != 0 {
            self.status.insert(Status::Negative);
        } else {
            self.status.remove(Status::Negative);
        }
    }

    pub fn update_zero_and_negative_flags(&mut self, result: u8) {
        self.update_zero_flag(result);
        self.update_negative_flag(result);
    }

    pub(super) fn get_operand_address(&mut self, mode: &AddressMode) -> u16 {
        match mode {
            AddressMode::Immediate => {
                let current = self.program_counter;
                self.program_counter += 1;
                current
            }
            AddressMode::ZeroPage => self.read_u8() as u16,
            AddressMode::ZeroPageX => self.read_u8().wrapping_add(self.register_x) as u16,
            AddressMode::ZeroPageY => self.read_u8().wrapping_add(self.register_y) as u16,
            AddressMode::Absolute => self.read_u16(),
            AddressMode::AbsoluteX => self.read_u16().wrapping_add(self.register_x as u16),
            AddressMode::AbsoluteY => self.read_u16().wrapping_add(self.register_y as u16),
            AddressMode::Indirect => {
                let address = self.read_u16();
                self.mem_read_u16(address)
            }
            AddressMode::IndirectX => {
                let base = self.read_u8().wrapping_add(self.register_x);
                self.mem_read_u16(base as u16)
            }
            AddressMode::IndirectY => {
                let base = self.read_u8();
                let address = self.mem_read_u16(base as u16);
                address.wrapping_add(self.register_y as u16)
            }
            _ => unreachable!(),
        }
    }

    pub(super) fn get_operand(&mut self, mode: &AddressMode) -> u8 {
        match mode {
            AddressMode::Accumulator => self.register_a,
            _ => {
                let operand = self.get_operand_address(mode);
                self.mem_read_u8(operand)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ASL Tests
    #[test]
    fn asl_accumulator() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x01;

        cpu.asl(&AddressMode::Accumulator);

        assert_eq!(cpu.register_a, 0x02);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn asl_accumulator_sets_carry() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x81; // 10000001

        cpu.asl(&AddressMode::Accumulator);

        assert_eq!(cpu.register_a, 0x02);
        assert_eq!(cpu.status, Status::Carry);
    }

    #[test]
    fn asl_accumulator_sets_zero() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x00;

        cpu.asl(&AddressMode::Accumulator);

        assert_eq!(cpu.register_a, 0x00);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn asl_accumulator_sets_negative() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x40; // Shift to get 10000000

        cpu.asl(&AddressMode::Accumulator);

        assert_eq!(cpu.register_a, 0x80);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn asl_zeropage() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x10, 0x01); // Value at address 0x10
        cpu.mem_write_u8(0x0800, 0x10); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.asl(&AddressMode::ZeroPage);

        assert_eq!(cpu.mem_read_u8(0x10), 0x02);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn asl_zeropage_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x05;
        cpu.mem_write_u8(0x15, 0x01); // Value at address 0x15 (0x10 + 0x05)
        cpu.mem_write_u8(0x0800, 0x10); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.asl(&AddressMode::ZeroPageX);

        assert_eq!(cpu.mem_read_u8(0x15), 0x02);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn asl_absolute() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x0200, 0x01); // Value at address 0x2000
        cpu.mem_write_u16(0x0800, 0x0200); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.asl(&AddressMode::Absolute);

        assert_eq!(cpu.mem_read_u8(0x0200), 0x02);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn asl_absolute_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x05;
        cpu.mem_write_u8(0x0205, 0x01); // Value at address 0x2005 (0x2000 + 0x05)
        cpu.mem_write_u16(0x0800, 0x0200); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.asl(&AddressMode::AbsoluteX);

        assert_eq!(cpu.mem_read_u8(0x0205), 0x02);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn asl_absolute_sets_carry_and_zero() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x0200, 0x80); // 10000000 -> 00000000 with carry
        cpu.mem_write_u16(0x0800, 0x0200); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.asl(&AddressMode::Absolute);

        assert_eq!(cpu.mem_read_u8(0x0200), 0x00);
        assert_eq!(cpu.status, Status::Carry | Status::Zero);
    }

    #[test]
    fn lda_immediate() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x0800, 0x05); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.lda(&AddressMode::Immediate);

        assert_eq!(cpu.register_a, 5);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn lda_immediate_zero() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x0800, 0x00); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.lda(&AddressMode::Immediate);

        assert_eq!(cpu.register_a, 0);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn lda_zeropage() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x05, 0x20); // Value at address 0x05
        cpu.mem_write_u8(0x0800, 0x05); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.lda(&AddressMode::ZeroPage);

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn lda_zeropage_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x05;
        cpu.mem_write_u8(0x0a, 0x20); // Value at address 0x0a (0x05 + 0x05)
        cpu.mem_write_u8(0x0800, 0x05); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.lda(&AddressMode::ZeroPageX);

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn lda_absolute() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x0205, 0x20); // Value at address 0x2005
        cpu.mem_write_u16(0x0800, 0x0205); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.lda(&AddressMode::Absolute);

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn lda_absolute_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x01;
        cpu.mem_write_u8(0x0206, 0x20); // Value at address 0x2006 (0x2005 + 0x01)
        cpu.mem_write_u16(0x0800, 0x0205); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.lda(&AddressMode::AbsoluteX);

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn lda_absolute_y() {
        let mut cpu = CPU::default();
        cpu.register_y = 0x01;
        cpu.mem_write_u8(0x0206, 0x20); // Value at address 0x2006 (0x2005 + 0x01)
        cpu.mem_write_u16(0x0800, 0x0205); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.lda(&AddressMode::AbsoluteY);

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn lda_indirect_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x01;
        cpu.mem_write_u8(0x06, 0x20); // Low byte of target address at 0x06 (0x05 + 0x01)
        cpu.mem_write_u8(0x07, 0x01); // High byte of target address at 0x07
        cpu.mem_write_u8(0x0120, 0x10); // Value at target address 0x1020
        cpu.mem_write_u8(0x0800, 0x05); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.lda(&AddressMode::IndirectX);

        assert_eq!(cpu.register_a, 0x10);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn lda_indirect_y() {
        let mut cpu = CPU::default();
        cpu.register_y = 0x01;
        cpu.mem_write_u16(0x05, 0x1020); // Base target address stored at 0x05
        cpu.mem_write_u8(0x1021, 0x10); // Value at target address 0x1021 (0x1020 + 0x01)
        cpu.mem_write_u8(0x0800, 0x05); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.lda(&AddressMode::IndirectY);

        assert_eq!(cpu.register_a, 0x10);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldx_immediate() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x0800, 0x05); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.ldx(&AddressMode::Immediate);

        assert_eq!(cpu.register_x, 5);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldx_zeropage() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x05, 0x20); // Value at address 0x05
        cpu.mem_write_u8(0x0800, 0x05); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.ldx(&AddressMode::ZeroPage);

        assert_eq!(cpu.register_x, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldx_zeropage_y() {
        let mut cpu = CPU::default();
        cpu.register_y = 0x05;
        cpu.mem_write_u8(0x0a, 0x20); // Value at address 0x0a (0x05 + 0x05)
        cpu.mem_write_u8(0x0800, 0x05); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.ldx(&AddressMode::ZeroPageY);

        assert_eq!(cpu.register_x, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldx_absolute() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x0205, 0x20); // Value at address 0x2005
        cpu.mem_write_u16(0x0800, 0x0205); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.ldx(&AddressMode::Absolute);

        assert_eq!(cpu.register_x, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldx_absolute_y() {
        let mut cpu = CPU::default();
        cpu.register_y = 0x01;
        cpu.mem_write_u8(0x0206, 0x20); // Value at address 0x2006 (0x2005 + 0x01)
        cpu.mem_write_u16(0x0800, 0x0205); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.ldx(&AddressMode::AbsoluteY);

        assert_eq!(cpu.register_x, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldy_immediate() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x0800, 0x05); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.ldy(&AddressMode::Immediate);

        assert_eq!(cpu.register_y, 5);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldy_zeropage() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x05, 0x20); // Value at address 0x05
        cpu.mem_write_u8(0x0800, 0x05); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.ldy(&AddressMode::ZeroPage);

        assert_eq!(cpu.register_y, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldy_zeropage_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x05;
        cpu.mem_write_u8(0x0a, 0x20); // Value at address 0x0a (0x05 + 0x05)
        cpu.mem_write_u8(0x0800, 0x05); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.ldy(&AddressMode::ZeroPageX);

        assert_eq!(cpu.register_y, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldy_absolute() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x0205, 0x20); // Value at address 0x2005
        cpu.mem_write_u16(0x0800, 0x0205); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.ldy(&AddressMode::Absolute);

        assert_eq!(cpu.register_y, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldy_absolute_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x01;
        cpu.mem_write_u8(0x0206, 0x20); // Value at address 0x2006 (0x2005 + 0x01)
        cpu.mem_write_u16(0x0800, 0x0205); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.ldy(&AddressMode::AbsoluteX);

        assert_eq!(cpu.register_y, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn and_immediate() {
        let mut cpu = CPU::default();
        cpu.register_a = 0xF0;
        cpu.mem_write_u8(0x0800, 0x10); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.and(&AddressMode::Immediate);

        assert_eq!(cpu.register_a, 0x10);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn and_zeropage() {
        let mut cpu = CPU::default();
        cpu.register_a = 0xF0;
        cpu.mem_write_u8(0x05, 0x20); // Value at address 0x05
        cpu.mem_write_u8(0x0800, 0x05); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.and(&AddressMode::ZeroPage);

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn and_zeropage_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x05;
        cpu.register_a = 0xF0;
        cpu.mem_write_u8(0x0a, 0x20); // Value at address 0x0a (0x05 + 0x05)
        cpu.mem_write_u8(0x0800, 0x05); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.and(&AddressMode::ZeroPageX);

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn and_absolute() {
        let mut cpu = CPU::default();
        cpu.register_a = 0xF0;
        cpu.mem_write_u8(0x0205, 0x20); // Value at address 0x2005
        cpu.mem_write_u16(0x0800, 0x0205); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.and(&AddressMode::Absolute);

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn and_absolute_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x01;
        cpu.register_a = 0xF0;
        cpu.mem_write_u8(0x0206, 0x20); // Value at address 0x2006 (0x2005 + 0x01)
        cpu.mem_write_u16(0x0800, 0x0205); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.and(&AddressMode::AbsoluteX);

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn and_absolute_y() {
        let mut cpu = CPU::default();
        cpu.register_y = 0x01;
        cpu.register_a = 0xF0;
        cpu.mem_write_u8(0x0206, 0x20); // Value at address 0x2006 (0x2005 + 0x01)
        cpu.mem_write_u16(0x0800, 0x0205); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.and(&AddressMode::AbsoluteY);

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn and_indirect_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x01;
        cpu.register_a = 0xF0;
        cpu.mem_write_u8(0x06, 0x20); // Low byte of target address at 0x06 (0x05 + 0x01)
        cpu.mem_write_u8(0x07, 0x01); // High byte of target address at 0x07
        cpu.mem_write_u8(0x0120, 0x10); // Value at target address 0x1020
        cpu.mem_write_u8(0x0800, 0x05); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.and(&AddressMode::IndirectX);

        assert_eq!(cpu.register_a, 0x10);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn and_indirect_y() {
        let mut cpu = CPU::default();
        cpu.register_y = 0x01;
        cpu.register_a = 0xF0;
        cpu.mem_write_u16(0x05, 0x0120); // Base target address stored at 0x05
        cpu.mem_write_u8(0x0121, 0x10); // Value at target address 0x1021 (0x1020 + 0x01)
        cpu.mem_write_u8(0x0800, 0x05); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.and(&AddressMode::IndirectY);

        assert_eq!(cpu.register_a, 0x10);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn adc_immediate() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x05;
        cpu.mem_write_u8(0x0800, 0x10); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.adc(&AddressMode::Immediate);

        assert_eq!(cpu.register_a, 0x15);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn adc_immediate_with_carry() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x05;
        cpu.status.insert(Status::Carry);
        cpu.mem_write_u8(0x0800, 0x10); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.adc(&AddressMode::Immediate);

        assert_eq!(cpu.register_a, 0x16);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn adc_immediate_with_overflow() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x50;
        cpu.mem_write_u8(0x0800, 0x70); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.adc(&AddressMode::Immediate);

        assert_eq!(cpu.register_a, 0xC0);
        assert_eq!(cpu.status, Status::Negative | Status::Overflow);
    }

    #[test]
    fn adc_immediate_with_carry_flag() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x01;
        cpu.mem_write_u8(0x0800, 0xFF); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.adc(&AddressMode::Immediate);

        assert_eq!(cpu.register_a, 0x00);
        assert_eq!(cpu.status, Status::Carry | Status::Zero);
    }

    #[test]
    fn adc_zeropage() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x05;
        cpu.mem_write_u8(0x05, 0x10); // Value at address 0x05
        cpu.mem_write_u8(0x0800, 0x05); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.adc(&AddressMode::ZeroPage);

        assert_eq!(cpu.register_a, 0x15);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn adc_zeropage_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x05;
        cpu.register_a = 0x05;
        cpu.mem_write_u8(0x0A, 0x10); // Value at address 0x0A (0x05 + 0x05)
        cpu.mem_write_u8(0x0800, 0x05); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.adc(&AddressMode::ZeroPageX);

        assert_eq!(cpu.register_a, 0x15);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn adc_absolute() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x05;
        cpu.mem_write_u8(0x0205, 0x10); // Value at address 0x2005
        cpu.mem_write_u16(0x0800, 0x0205); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.adc(&AddressMode::Absolute);

        assert_eq!(cpu.register_a, 0x15);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn adc_absolute_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x01;
        cpu.register_a = 0x05;
        cpu.mem_write_u8(0x0206, 0x10); // Value at address 0x2006 (0x2005 + 0x01)
        cpu.mem_write_u16(0x0800, 0x0205); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.adc(&AddressMode::AbsoluteX);

        assert_eq!(cpu.register_a, 0x15);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn adc_absolute_y() {
        let mut cpu = CPU::default();
        cpu.register_y = 0x01;
        cpu.register_a = 0x05;
        cpu.mem_write_u8(0x0206, 0x10); // Value at address 0x2006 (0x2005 + 0x01)
        cpu.mem_write_u16(0x0800, 0x0205); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.adc(&AddressMode::AbsoluteY);

        assert_eq!(cpu.register_a, 0x15);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn adc_indirect_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x01;
        cpu.register_a = 0x05;
        cpu.mem_write_u8(0x06, 0x20); // Low byte of target address at 0x06 (0x05 + 0x01)
        cpu.mem_write_u8(0x07, 0x01); // High byte of target address at 0x07
        cpu.mem_write_u8(0x0120, 0x10); // Value at target address 0x1020
        cpu.mem_write_u8(0x0800, 0x05); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.adc(&AddressMode::IndirectX);

        assert_eq!(cpu.register_a, 0x15);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn adc_indirect_y() {
        let mut cpu = CPU::default();
        cpu.register_y = 0x01;
        cpu.register_a = 0x05;
        cpu.mem_write_u16(0x05, 0x0120); // Base target address stored at 0x05
        cpu.mem_write_u8(0x0121, 0x10); // Value at target address 0x1021 (0x1020 + 0x01)
        cpu.mem_write_u8(0x0800, 0x05); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.adc(&AddressMode::IndirectY);

        assert_eq!(cpu.register_a, 0x15);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn sta_zeropage() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x20;
        cpu.mem_write_u8(0x0800, 0x12); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.sta(&AddressMode::ZeroPage);

        assert_eq!(cpu.mem_read_u8(0x12), 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn sta_zeropage_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x05;
        cpu.register_a = 0x20;
        cpu.mem_write_u8(0x0800, 0x12); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.sta(&AddressMode::ZeroPageX);

        assert_eq!(cpu.mem_read_u8(0x17), 0x20); // 0x12 + 0x05 = 0x17
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn sta_absolute() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x20;
        cpu.mem_write_u16(0x0800, 0x0205); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.sta(&AddressMode::Absolute);

        assert_eq!(cpu.mem_read_u8(0x0205), 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn sta_absolute_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x01;
        cpu.register_a = 0x20;
        cpu.mem_write_u16(0x0800, 0x0205); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.sta(&AddressMode::AbsoluteX);

        assert_eq!(cpu.mem_read_u8(0x0206), 0x20); // 0x2005 + 0x01 = 0x2006
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn sta_absolute_y() {
        let mut cpu = CPU::default();
        cpu.register_y = 0x01;
        cpu.register_a = 0x20;
        cpu.mem_write_u16(0x0800, 0x0205); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.sta(&AddressMode::AbsoluteY);

        assert_eq!(cpu.mem_read_u8(0x0206), 0x20); // 0x2005 + 0x01 = 0x2006
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn sta_indirect_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x01;
        cpu.register_a = 0x20;
        cpu.mem_write_u16(0x06, 0x0206); // Target address at 0x06 (0x05 + 0x01)
        cpu.mem_write_u8(0x0800, 0x05); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.sta(&AddressMode::IndirectX);

        assert_eq!(cpu.mem_read_u8(0x0206), 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn sta_indirect_y() {
        let mut cpu = CPU::default();
        cpu.register_y = 0x01;
        cpu.register_a = 0x20;
        cpu.mem_write_u16(0x05, 0x0205); // Base target address at 0x05
        cpu.mem_write_u8(0x0800, 0x05); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.sta(&AddressMode::IndirectY);

        assert_eq!(cpu.mem_read_u8(0x0206), 0x20); // 0x2005 + 0x01 = 0x2006
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn tax() {
        let mut cpu = CPU::default();
        cpu.register_a = 10;

        cpu.tax();

        assert_eq!(cpu.register_x, 10);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn tax_zero_flag() {
        let mut cpu = CPU::default();
        cpu.register_a = 0;

        cpu.tax();

        assert_eq!(cpu.register_x, 0);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn tax_negative_flag() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x80;

        cpu.tax();

        assert_eq!(cpu.register_x, 0x80);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn tay() {
        let mut cpu = CPU::default();
        cpu.register_a = 10;

        cpu.tay();

        assert_eq!(cpu.register_y, 10);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn tay_zero_flag() {
        let mut cpu = CPU::default();
        cpu.register_a = 0;

        cpu.tay();

        assert_eq!(cpu.register_y, 0);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn tay_negative_flag() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x80;

        cpu.tay();

        assert_eq!(cpu.register_y, 0x80);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn txa() {
        let mut cpu = CPU::default();
        cpu.register_x = 10;

        cpu.txa();

        assert_eq!(cpu.register_a, 10);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn txa_zero_flag() {
        let mut cpu = CPU::default();
        cpu.register_x = 0;

        cpu.txa();

        assert_eq!(cpu.register_a, 0);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn txa_negative_flag() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x80;

        cpu.txa();

        assert_eq!(cpu.register_a, 0x80);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn tya() {
        let mut cpu = CPU::default();
        cpu.register_y = 10;

        cpu.tya();

        assert_eq!(cpu.register_a, 10);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn tya_zero_flag() {
        let mut cpu = CPU::default();
        cpu.register_y = 0;

        cpu.tya();

        assert_eq!(cpu.register_a, 0);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn tya_negative_flag() {
        let mut cpu = CPU::default();
        cpu.register_y = 0x80;

        cpu.tya();

        assert_eq!(cpu.register_a, 0x80);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn inx() {
        let mut cpu = CPU::default();
        cpu.register_x = 5;

        cpu.inx();

        assert_eq!(cpu.register_x, 6);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn inx_overflow() {
        let mut cpu = CPU::default();
        cpu.register_x = 0xff;

        cpu.inx();

        assert_eq!(cpu.register_x, 0x00);
        assert_eq!(cpu.status, Status::Zero);
    }
    #[test]
    fn iny() {
        let mut cpu = CPU::default();
        cpu.register_y = 5;

        cpu.iny();

        assert_eq!(cpu.register_y, 6);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn iny_overflow() {
        let mut cpu = CPU::default();
        cpu.register_y = 0xff;

        cpu.iny();

        assert_eq!(cpu.register_y, 0x00);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn inc_zeropage() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x10, 0x05); // Value at address 0x10
        cpu.mem_write_u8(0x0800, 0x10); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.inc(&AddressMode::ZeroPage);

        assert_eq!(cpu.mem_read_u8(0x10), 0x06);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn inc_zeropage_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x05;
        cpu.mem_write_u8(0x15, 0x05); // Value at address 0x15 (0x10 + 0x05)
        cpu.mem_write_u8(0x0800, 0x10); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.inc(&AddressMode::ZeroPageX);

        assert_eq!(cpu.mem_read_u8(0x15), 0x06);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn inc_absolute() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x0200, 0x05); // Value at address 0x2000
        cpu.mem_write_u16(0x0800, 0x0200); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.inc(&AddressMode::Absolute);

        assert_eq!(cpu.mem_read_u8(0x0200), 0x06);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn inc_absolute_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x05;
        cpu.mem_write_u8(0x0205, 0x05); // Value at address 0x2005 (0x2000 + 0x05)
        cpu.mem_write_u16(0x0800, 0x0200); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.inc(&AddressMode::AbsoluteX);

        assert_eq!(cpu.mem_read_u8(0x0205), 0x06);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn inc_overflow() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x10, 0xFF); // Value at address 0x10
        cpu.mem_write_u8(0x0800, 0x10); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.inc(&AddressMode::ZeroPage);

        assert_eq!(cpu.mem_read_u8(0x10), 0x00);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn inc_negative_flag() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x10, 0x7F); // 127 -> 128 (0x80)
        cpu.mem_write_u8(0x0800, 0x10); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.inc(&AddressMode::ZeroPage);

        assert_eq!(cpu.mem_read_u8(0x10), 0x80);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn dex_decrements_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x05;

        cpu.dex();

        assert_eq!(cpu.register_x, 0x04);
        assert!(!cpu.status.contains(Status::Zero));
        assert!(!cpu.status.contains(Status::Negative));
    }

    #[test]
    fn dex_sets_zero_flag() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x01;

        cpu.dex();

        assert_eq!(cpu.register_x, 0x00);
        assert!(cpu.status.contains(Status::Zero));
        assert!(!cpu.status.contains(Status::Negative));
    }

    #[test]
    fn dex_sets_negative_flag() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x00;

        cpu.dex();

        assert_eq!(cpu.register_x, 0xFF);
        assert!(!cpu.status.contains(Status::Zero));
        assert!(cpu.status.contains(Status::Negative));
    }

    #[test]
    fn dey_decrements_y() {
        let mut cpu = CPU::default();
        cpu.register_y = 0x05;

        cpu.dey();

        assert_eq!(cpu.register_y, 0x04);
        assert!(!cpu.status.contains(Status::Zero));
        assert!(!cpu.status.contains(Status::Negative));
    }

    #[test]
    fn dey_sets_zero_flag() {
        let mut cpu = CPU::default();
        cpu.register_y = 0x01;

        cpu.dey();

        assert_eq!(cpu.register_y, 0x00);
        assert!(cpu.status.contains(Status::Zero));
        assert!(!cpu.status.contains(Status::Negative));
    }

    #[test]
    fn dey_sets_negative_flag() {
        let mut cpu = CPU::default();
        cpu.register_y = 0x00;

        cpu.dey();

        assert_eq!(cpu.register_y, 0xFF);
        assert!(!cpu.status.contains(Status::Zero));
        assert!(cpu.status.contains(Status::Negative));
    }

    #[test]
    fn dec_zeropage() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x10, 0x05); // Value at address 0x10
        cpu.mem_write_u8(0x0800, 0x10); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.dec(&AddressMode::ZeroPage);

        assert_eq!(cpu.mem_read_u8(0x10), 0x04);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn dec_zeropage_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x05;
        cpu.mem_write_u8(0x15, 0x05); // Value at address 0x15 (0x10 + 0x05)
        cpu.mem_write_u8(0x0800, 0x10); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.dec(&AddressMode::ZeroPageX);

        assert_eq!(cpu.mem_read_u8(0x15), 0x04);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn dec_absolute() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x0200, 0x05); // Value at address 0x2000
        cpu.mem_write_u16(0x0800, 0x0200); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.dec(&AddressMode::Absolute);

        assert_eq!(cpu.mem_read_u8(0x0200), 0x04);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn dec_absolute_x() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x05;
        cpu.mem_write_u8(0x0205, 0x05); // Value at address 0x2005 (0x2000 + 0x05)
        cpu.mem_write_u16(0x0800, 0x0200); // Base address operand at PC
        cpu.program_counter = 0x0800;

        cpu.dec(&AddressMode::AbsoluteX);

        assert_eq!(cpu.mem_read_u8(0x0205), 0x04);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn dec_underflow() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x10, 0x00); // Value at address 0x10
        cpu.mem_write_u8(0x0800, 0x10); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.dec(&AddressMode::ZeroPage);

        assert_eq!(cpu.mem_read_u8(0x10), 0xFF);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn dec_sets_zero_flag() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x10, 0x01); // Value at address 0x10
        cpu.mem_write_u8(0x0800, 0x10); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.dec(&AddressMode::ZeroPage);

        assert_eq!(cpu.mem_read_u8(0x10), 0x00);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn dec_negative_flag() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x10, 0x81); // 129 -> 128 (0x80)
        cpu.mem_write_u8(0x0800, 0x10); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.dec(&AddressMode::ZeroPage);

        assert_eq!(cpu.mem_read_u8(0x10), 0x80);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn tsx() {
        let mut cpu = CPU::default();
        cpu.stack_pointer = 0x50;

        cpu.tsx();

        assert_eq!(cpu.register_x, 0x50);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn tsx_zero_flag() {
        let mut cpu = CPU::default();
        cpu.stack_pointer = 0x00;

        cpu.tsx();

        assert_eq!(cpu.register_x, 0x00);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn tsx_negative_flag() {
        let mut cpu = CPU::default();
        cpu.stack_pointer = 0x80;

        cpu.tsx();

        assert_eq!(cpu.register_x, 0x80);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn txs() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x50;

        cpu.txs();

        assert_eq!(cpu.stack_pointer, 0x50);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn txs_zero_flag() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x00;

        cpu.txs();

        assert_eq!(cpu.stack_pointer, 0x00);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn txs_negative_flag() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x80;

        cpu.txs();

        assert_eq!(cpu.stack_pointer, 0x80);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn pha() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x42;

        cpu.pha();

        assert_eq!(cpu.mem_read_u8(0x01FF), 0x42);
        assert_eq!(cpu.stack_pointer, 0xFE);
    }

    #[test]
    fn pla() {
        let mut cpu = CPU::default();
        cpu.stack_pointer = 0xFE;
        cpu.mem_write_u8(0x01FF, 0x42);

        cpu.pla();

        assert_eq!(cpu.register_a, 0x42);
        assert_eq!(cpu.stack_pointer, 0xFF);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn pla_zero_flag() {
        let mut cpu = CPU::default();
        cpu.stack_pointer = 0xFE;
        cpu.mem_write_u8(0x01FF, 0x00);

        cpu.pla();

        assert_eq!(cpu.register_a, 0x00);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn pla_negative_flag() {
        let mut cpu = CPU::default();
        cpu.stack_pointer = 0xFE;
        cpu.mem_write_u8(0x01FF, 0x80);

        cpu.pla();

        assert_eq!(cpu.register_a, 0x80);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn php() {
        let mut cpu = CPU::default();
        cpu.status = Status::Carry | Status::Zero;

        cpu.php();

        assert_eq!(
            cpu.mem_read_u8(0x01FF),
            (Status::Carry | Status::Zero).bits()
        );
        assert_eq!(cpu.stack_pointer, 0xFE);
    }

    #[test]
    fn plp() {
        let mut cpu = CPU::default();
        cpu.stack_pointer = 0xFE;
        cpu.mem_write_u8(0x01FF, (Status::Carry | Status::Zero).bits());

        cpu.plp();

        assert_eq!(cpu.status, Status::Carry | Status::Zero);
        assert_eq!(cpu.stack_pointer, 0xFF);
    }

    #[test]
    fn eor_immediate() {
        let mut cpu = CPU::default();
        cpu.register_a = 0xF0;
        cpu.mem_write_u8(0x0800, 0x0F); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.eor(&AddressMode::Immediate);

        assert_eq!(cpu.register_a, 0xFF);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn eor_zero_flag() {
        let mut cpu = CPU::default();
        cpu.register_a = 0xFF;
        cpu.mem_write_u8(0x0800, 0xFF); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.eor(&AddressMode::Immediate);

        assert_eq!(cpu.register_a, 0x00);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn eor_zeropage() {
        let mut cpu = CPU::default();
        cpu.register_a = 0xF0;
        cpu.mem_write_u8(0x05, 0x0F); // Value at address 0x05
        cpu.mem_write_u8(0x0800, 0x05); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.eor(&AddressMode::ZeroPage);

        assert_eq!(cpu.register_a, 0xFF);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn ora_immediate() {
        let mut cpu = CPU::default();
        cpu.register_a = 0xF0;
        cpu.mem_write_u8(0x0800, 0x0F); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.ora(&AddressMode::Immediate);

        assert_eq!(cpu.register_a, 0xFF);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn ora_zero_flag() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x00;
        cpu.mem_write_u8(0x0800, 0x00); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.ora(&AddressMode::Immediate);

        assert_eq!(cpu.register_a, 0x00);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn ora_zeropage() {
        let mut cpu = CPU::default();
        cpu.register_a = 0xF0;
        cpu.mem_write_u8(0x05, 0x0F); // Value at address 0x05
        cpu.mem_write_u8(0x0800, 0x05); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.ora(&AddressMode::ZeroPage);

        assert_eq!(cpu.register_a, 0xFF);
        assert_eq!(cpu.status, Status::Negative);
    }

    // Jump Operations Tests
    #[test]
    fn jmp_absolute() {
        let mut cpu = CPU::default();
        cpu.mem_write_u16(0x0800, 0x1234); // Target address at PC
        cpu.program_counter = 0x0800;

        cpu.jmp(&AddressMode::Absolute);

        assert_eq!(cpu.program_counter, 0x1234);
    }

    #[test]
    fn jmp_indirect() {
        let mut cpu = CPU::default();
        cpu.mem_write_u16(0x1234, 0x5678); // Target address stored at 0x1234
        cpu.mem_write_u16(0x0800, 0x1234); // Pointer address at PC
        cpu.program_counter = 0x0800;

        cpu.jmp(&AddressMode::Indirect);

        assert_eq!(cpu.program_counter, 0x5678);
    }

    #[test]
    fn jsr_pushes_return_address() {
        let mut cpu = CPU::default();
        cpu.program_counter = 0x0800;
        cpu.mem_write_u16(0x0800, 0x1234); // Target address at PC

        cpu.jsr(&AddressMode::Absolute);

        assert_eq!(cpu.program_counter, 0x1234);
        assert_eq!(cpu.stack_pointer, 0xFD);

        // Check that return address - 1 was pushed to stack
        let return_addr = cpu.stack_pop_u16();
        assert_eq!(return_addr, 0x0801); // PC + 2 - 1 = 0x0800 + 2 - 1
    }

    #[test]
    fn rts_returns_to_caller() {
        let mut cpu = CPU::default();
        cpu.stack_push_u16(0x1234);

        cpu.rts();

        assert_eq!(cpu.program_counter, 0x1235);
        assert_eq!(cpu.stack_pointer, 0xFF);
    }

    #[test]
    fn rti_restores_status_and_pc() {
        let mut cpu = CPU::default();
        cpu.stack_push_u16(0x1234); // PC pushed first
        cpu.stack_push(0b10010001); // Status pushed second (will be popped first)

        cpu.rti();

        assert_eq!(cpu.program_counter, 0x1234);
        assert_eq!(cpu.status.bits(), 0b10010001);
        assert_eq!(cpu.stack_pointer, 0xFF);
    }

    #[test]
    fn jsr_rts_sequence() {
        let mut cpu = CPU::default();
        cpu.program_counter = 0x0800;
        cpu.stack_pointer = 0xFF;

        cpu.stack_push_u16(0x0802);
        cpu.rts();
        assert_eq!(cpu.program_counter, 0x0803);
        assert_eq!(cpu.stack_pointer, 0xFF);
    }

    // Status Flag Operations Tests
    #[test]
    fn clc_clears_carry() {
        let mut cpu = CPU::default();
        cpu.status.insert(Status::Carry);

        cpu.clc();

        assert!(!cpu.status.contains(Status::Carry));
    }

    #[test]
    fn sec_sets_carry() {
        let mut cpu = CPU::default();

        cpu.sec();

        assert!(cpu.status.contains(Status::Carry));
    }

    #[test]
    fn cli_clears_interrupt_disable() {
        let mut cpu = CPU::default();
        cpu.status.insert(Status::InterruptDisable);

        cpu.cli();

        assert!(!cpu.status.contains(Status::InterruptDisable));
    }

    #[test]
    fn sei_sets_interrupt_disable() {
        let mut cpu = CPU::default();

        cpu.sei();

        assert!(cpu.status.contains(Status::InterruptDisable));
    }

    #[test]
    fn cld_clears_decimal() {
        let mut cpu = CPU::default();
        cpu.status.insert(Status::Decimal);

        cpu.cld();

        assert!(!cpu.status.contains(Status::Decimal));
    }

    #[test]
    fn sed_sets_decimal() {
        let mut cpu = CPU::default();

        cpu.sed();

        assert!(cpu.status.contains(Status::Decimal));
    }

    #[test]
    fn clv_clears_overflow() {
        let mut cpu = CPU::default();
        cpu.status.insert(Status::Overflow);

        cpu.clv();

        assert!(!cpu.status.contains(Status::Overflow));
    }

    #[test]
    fn flag_operations_dont_affect_other_flags() {
        let mut cpu = CPU::default();
        cpu.status = Status::Carry | Status::Zero | Status::Negative;

        cpu.clc();

        assert!(!cpu.status.contains(Status::Carry));
        assert!(cpu.status.contains(Status::Zero));
        assert!(cpu.status.contains(Status::Negative));
    }

    #[test]
    fn indirect_addressing_mode() {
        let mut cpu = CPU::default();
        cpu.program_counter = 0x0800;
        cpu.mem_write_u16(0x0800, 0x0900); // Pointer address at PC
        cpu.mem_write_u16(0x0900, 0x0A00); // Target address at pointer location

        let address = cpu.get_operand_address(&AddressMode::Indirect);
        assert_eq!(address, 0x0A00);
        assert_eq!(cpu.program_counter, 0x0802);
    }

    // SBC Tests
    #[test]
    fn sbc_immediate() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x50;
        cpu.status.insert(Status::Carry); // No borrow
        cpu.mem_write_u8(0x0800, 0x30); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.sbc(&AddressMode::Immediate);

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.contains(Status::Carry)); // No borrow
        assert!(!cpu.status.contains(Status::Zero));
        assert!(!cpu.status.contains(Status::Negative));
    }

    #[test]
    fn sbc_immediate_with_borrow() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x50;
        cpu.status.remove(Status::Carry); // Borrow
        cpu.mem_write_u8(0x0800, 0x30); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.sbc(&AddressMode::Immediate);

        assert_eq!(cpu.register_a, 0x1F);
        assert!(cpu.status.contains(Status::Carry)); // No borrow after operation
    }

    #[test]
    fn sbc_sets_zero_flag() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x30;
        cpu.status.insert(Status::Carry); // No borrow
        cpu.mem_write_u8(0x0800, 0x30); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.sbc(&AddressMode::Immediate);

        assert_eq!(cpu.register_a, 0x00);
        assert!(cpu.status.contains(Status::Zero));
        assert!(cpu.status.contains(Status::Carry));
    }

    #[test]
    fn sbc_sets_negative_flag() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x30;
        cpu.status.insert(Status::Carry); // No borrow
        cpu.mem_write_u8(0x0800, 0x40); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.sbc(&AddressMode::Immediate);

        assert_eq!(cpu.register_a, 0xF0);
        assert!(!cpu.status.contains(Status::Carry)); // Borrow occurred
        assert!(cpu.status.contains(Status::Negative));
    }

    // CMP Tests
    #[test]
    fn cmp_immediate_equal() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x30;
        cpu.mem_write_u8(0x0800, 0x30); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.cmp(&AddressMode::Immediate);

        assert!(cpu.status.contains(Status::Zero));
        assert!(cpu.status.contains(Status::Carry));
        assert!(!cpu.status.contains(Status::Negative));
    }

    #[test]
    fn cmp_immediate_greater() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x50;
        cpu.mem_write_u8(0x0800, 0x30); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.cmp(&AddressMode::Immediate);

        assert!(!cpu.status.contains(Status::Zero));
        assert!(cpu.status.contains(Status::Carry));
        assert!(!cpu.status.contains(Status::Negative));
    }

    #[test]
    fn cmp_immediate_less() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x30;
        cpu.mem_write_u8(0x0800, 0x50); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.cmp(&AddressMode::Immediate);

        assert!(!cpu.status.contains(Status::Zero));
        assert!(!cpu.status.contains(Status::Carry));
        assert!(!cpu.status.contains(Status::Negative));
    }

    #[test]
    fn cmp_zeropage() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x50;
        cpu.mem_write_u8(0x05, 0x30); // Value at address 0x05
        cpu.mem_write_u8(0x0800, 0x05); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.cmp(&AddressMode::ZeroPage);

        assert!(!cpu.status.contains(Status::Zero));
        assert!(cpu.status.contains(Status::Carry));
    }

    // CPX Tests
    #[test]
    fn cpx_immediate_equal() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x30;
        cpu.mem_write_u8(0x0800, 0x30); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.cpx(&AddressMode::Immediate);

        assert!(cpu.status.contains(Status::Zero));
        assert!(cpu.status.contains(Status::Carry));
    }

    #[test]
    fn cpx_immediate_greater() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x50;
        cpu.mem_write_u8(0x0800, 0x30); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.cpx(&AddressMode::Immediate);

        assert!(!cpu.status.contains(Status::Zero));
        assert!(cpu.status.contains(Status::Carry));
    }

    #[test]
    fn cpx_zeropage() {
        let mut cpu = CPU::default();
        cpu.register_x = 0x50;
        cpu.mem_write_u8(0x05, 0x30); // Value at address 0x05
        cpu.mem_write_u8(0x0800, 0x05); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.cpx(&AddressMode::ZeroPage);

        assert!(!cpu.status.contains(Status::Zero));
        assert!(cpu.status.contains(Status::Carry));
    }

    // CPY Tests
    #[test]
    fn cpy_immediate_equal() {
        let mut cpu = CPU::default();
        cpu.register_y = 0x30;
        cpu.mem_write_u8(0x0800, 0x30); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.cpy(&AddressMode::Immediate);

        assert!(cpu.status.contains(Status::Zero));
        assert!(cpu.status.contains(Status::Carry));
    }

    #[test]
    fn cpy_immediate_less() {
        let mut cpu = CPU::default();
        cpu.register_y = 0x30;
        cpu.mem_write_u8(0x0800, 0x50); // Immediate value at PC
        cpu.program_counter = 0x0800;

        cpu.cpy(&AddressMode::Immediate);

        assert!(!cpu.status.contains(Status::Zero));
        assert!(!cpu.status.contains(Status::Carry));
    }

    // LSR Tests
    #[test]
    fn lsr_accumulator() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x02;

        cpu.lsr(&AddressMode::Accumulator);

        assert_eq!(cpu.register_a, 0x01);
        assert!(!cpu.status.contains(Status::Carry));
        assert!(!cpu.status.contains(Status::Zero));
        assert!(!cpu.status.contains(Status::Negative));
    }

    #[test]
    fn lsr_accumulator_sets_carry() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x03; // 00000011

        cpu.lsr(&AddressMode::Accumulator);

        assert_eq!(cpu.register_a, 0x01);
        assert!(cpu.status.contains(Status::Carry));
    }

    #[test]
    fn lsr_accumulator_sets_zero() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x01;

        cpu.lsr(&AddressMode::Accumulator);

        assert_eq!(cpu.register_a, 0x00);
        assert!(cpu.status.contains(Status::Zero));
        assert!(cpu.status.contains(Status::Carry));
    }

    #[test]
    fn lsr_zeropage() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x10, 0x02); // Value at address 0x10
        cpu.mem_write_u8(0x0800, 0x10); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.lsr(&AddressMode::ZeroPage);

        assert_eq!(cpu.mem_read_u8(0x10), 0x01);
        assert!(!cpu.status.contains(Status::Carry));
        assert!(!cpu.status.contains(Status::Zero));
    }

    // ROL Tests
    #[test]
    fn rol_accumulator() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x01;
        cpu.status.insert(Status::Carry);

        cpu.rol(&AddressMode::Accumulator);

        assert_eq!(cpu.register_a, 0x03); // 0x01 << 1 | 1
        assert!(!cpu.status.contains(Status::Carry));
    }

    #[test]
    fn rol_accumulator_sets_carry() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x81; // 10000001

        cpu.rol(&AddressMode::Accumulator);

        assert_eq!(cpu.register_a, 0x02);
        assert!(cpu.status.contains(Status::Carry));
    }

    #[test]
    fn rol_zeropage() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x10, 0x01); // Value at address 0x10
        cpu.mem_write_u8(0x0800, 0x10); // Address operand at PC
        cpu.program_counter = 0x0800;
        cpu.status.insert(Status::Carry);

        cpu.rol(&AddressMode::ZeroPage);

        assert_eq!(cpu.mem_read_u8(0x10), 0x03);
        assert!(!cpu.status.contains(Status::Carry));
    }

    // ROR Tests
    #[test]
    fn ror_accumulator() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x02;
        cpu.status.insert(Status::Carry);

        cpu.ror(&AddressMode::Accumulator);

        assert_eq!(cpu.register_a, 0x81); // 0x02 >> 1 | (1 << 7)
        assert!(!cpu.status.contains(Status::Carry));
        assert!(cpu.status.contains(Status::Negative));
    }

    #[test]
    fn ror_accumulator_sets_carry() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x03; // 00000011

        cpu.ror(&AddressMode::Accumulator);

        assert_eq!(cpu.register_a, 0x01);
        assert!(cpu.status.contains(Status::Carry));
    }

    #[test]
    fn ror_zeropage() {
        let mut cpu = CPU::default();
        cpu.mem_write_u8(0x10, 0x02); // Value at address 0x10
        cpu.mem_write_u8(0x0800, 0x10); // Address operand at PC
        cpu.program_counter = 0x0800;
        cpu.status.insert(Status::Carry);

        cpu.ror(&AddressMode::ZeroPage);

        assert_eq!(cpu.mem_read_u8(0x10), 0x81);
        assert!(!cpu.status.contains(Status::Carry));
    }

    // Branch Tests
    #[test]
    fn bcc_takes_branch_when_carry_clear() {
        let mut cpu = CPU::default();
        cpu.program_counter = 0x0800;
        cpu.status.remove(Status::Carry);
        cpu.mem_write_u8(0x0800, 0x05); // Offset

        cpu.bcc();

        assert_eq!(cpu.program_counter, 0x0806); // 0x0800 + 5 + 1 (auto increment)
    }

    #[test]
    fn bcc_no_branch_when_carry_set() {
        let mut cpu = CPU::default();
        cpu.program_counter = 0x0800;
        cpu.status.insert(Status::Carry);
        cpu.mem_write_u8(0x0800, 0x05); // Offset

        cpu.bcc();

        assert_eq!(cpu.program_counter, 0x0801); // Only incremented by read_u8
    }

    #[test]
    fn bcs_takes_branch_when_carry_set() {
        let mut cpu = CPU::default();
        cpu.program_counter = 0x0800;
        cpu.status.insert(Status::Carry);
        cpu.mem_write_u8(0x0800, 0x05); // Offset

        cpu.bcs();

        assert_eq!(cpu.program_counter, 0x0806);
    }

    #[test]
    fn beq_takes_branch_when_zero_set() {
        let mut cpu = CPU::default();
        cpu.program_counter = 0x0800;
        cpu.status.insert(Status::Zero);
        cpu.mem_write_u8(0x0800, 0x05); // Offset

        cpu.beq();

        assert_eq!(cpu.program_counter, 0x0806);
    }

    #[test]
    fn bne_takes_branch_when_zero_clear() {
        let mut cpu = CPU::default();
        cpu.program_counter = 0x0800;
        cpu.status.remove(Status::Zero);
        cpu.mem_write_u8(0x0800, 0x05); // Offset

        cpu.bne();

        assert_eq!(cpu.program_counter, 0x0806);
    }

    #[test]
    fn bmi_takes_branch_when_negative_set() {
        let mut cpu = CPU::default();
        cpu.program_counter = 0x0800;
        cpu.status.insert(Status::Negative);
        cpu.mem_write_u8(0x0800, 0x05); // Offset

        cpu.bmi();

        assert_eq!(cpu.program_counter, 0x0806);
    }

    #[test]
    fn bpl_takes_branch_when_negative_clear() {
        let mut cpu = CPU::default();
        cpu.program_counter = 0x0800;
        cpu.status.remove(Status::Negative);
        cpu.mem_write_u8(0x0800, 0x05); // Offset

        cpu.bpl();

        assert_eq!(cpu.program_counter, 0x0806);
    }

    #[test]
    fn bvc_takes_branch_when_overflow_clear() {
        let mut cpu = CPU::default();
        cpu.program_counter = 0x0800;
        cpu.status.remove(Status::Overflow);
        cpu.mem_write_u8(0x0800, 0x05); // Offset

        cpu.bvc();

        assert_eq!(cpu.program_counter, 0x0806);
    }

    #[test]
    fn bvs_takes_branch_when_overflow_set() {
        let mut cpu = CPU::default();
        cpu.program_counter = 0x0800;
        cpu.status.insert(Status::Overflow);
        cpu.mem_write_u8(0x0800, 0x05); // Offset

        cpu.bvs();

        assert_eq!(cpu.program_counter, 0x0806);
    }

    #[test]
    fn branch_backwards() {
        let mut cpu = CPU::default();
        cpu.program_counter = 0x0800;
        cpu.status.insert(Status::Zero);
        cpu.mem_write_u8(0x0800, 0xFB); // -5 in two's complement

        cpu.beq();

        assert_eq!(cpu.program_counter, 0x07FC); // 0x0800 + (-5) + 1
    }

    #[test]
    fn branch_no_condition() {
        let mut cpu = CPU::default();
        cpu.program_counter = 0x0800;
        cpu.status.remove(Status::Zero);
        cpu.mem_write_u8(0x0800, 0x05); // Offset

        cpu.beq();

        assert_eq!(cpu.program_counter, 0x0801); // Only incremented by read_u8
    }

    // BIT Tests
    #[test]
    fn bit_zeropage() {
        let mut cpu = CPU::default();
        cpu.register_a = 0xF0;
        cpu.mem_write_u8(0x05, 0xF0); // Value at address 0x05
        cpu.mem_write_u8(0x0800, 0x05); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.bit(&AddressMode::ZeroPage);

        assert!(!cpu.status.contains(Status::Zero)); // F0 & F0 = F0 != 0
        assert!(cpu.status.contains(Status::Negative)); // Bit 7 of operand is set
        assert!(cpu.status.contains(Status::Overflow)); // Bit 6 of operand is set
    }

    #[test]
    fn bit_zeropage_sets_zero() {
        let mut cpu = CPU::default();
        cpu.register_a = 0x0F;
        cpu.mem_write_u8(0x05, 0xF0); // Value at address 0x05
        cpu.mem_write_u8(0x0800, 0x05); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.bit(&AddressMode::ZeroPage);

        assert!(cpu.status.contains(Status::Zero)); // 0F & F0 = 00
        assert!(cpu.status.contains(Status::Negative)); // Bit 7 of operand is set
        assert!(cpu.status.contains(Status::Overflow)); // Bit 6 of operand is set
    }

    #[test]
    fn bit_clears_flags() {
        let mut cpu = CPU::default();
        cpu.register_a = 0xFF;
        cpu.mem_write_u8(0x05, 0x3F); // Value at address 0x05 (bits 7,6 clear)
        cpu.mem_write_u8(0x0800, 0x05); // Address operand at PC
        cpu.program_counter = 0x0800;

        cpu.bit(&AddressMode::ZeroPage);

        assert!(!cpu.status.contains(Status::Zero)); // FF & 3F = 3F != 0
        assert!(!cpu.status.contains(Status::Negative)); // Bit 7 of operand is clear
        assert!(!cpu.status.contains(Status::Overflow)); // Bit 6 of operand is clear
    }

    #[test]
    fn jmp_absolute_test() {
        let mut cpu = CPU::default();
        cpu.program_counter = 0x0800;
        cpu.mem_write_u8(0x0800, 0x34); // Low byte of target address
        cpu.mem_write_u8(0x0801, 0x12); // High byte of target address

        cpu.jmp(&AddressMode::Absolute);

        assert_eq!(cpu.program_counter, 0x1234);
    }

    #[test]
    fn jmp_game_scenario() {
        let mut cpu = CPU::default();
        cpu.program_counter = 0x06bf;
        cpu.mem_write_u8(0x06bf, 0x4c); // JMP instruction
        cpu.mem_write_u8(0x06c0, 0x35); // Low byte of target address
        cpu.mem_write_u8(0x06c1, 0x07); // High byte of target address

        // Simulate the instruction read that happens in run loop
        let instruction = cpu.read_u8(); // This should read 0x4c and set PC to 0x06c0
        assert_eq!(instruction, 0x4c);
        assert_eq!(cpu.program_counter, 0x06c0);

        cpu.jmp(&AddressMode::Absolute);

        assert_eq!(cpu.program_counter, 0x0735);
    }
}
