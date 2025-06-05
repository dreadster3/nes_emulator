use bitflags::bitflags;
use derivative::Derivative;
use thiserror::Error;

use crate::opcodes::{AddressMode, Mnemonic, OPCODE_MAP};

bitflags! {
    #[derive(Debug, Default, Eq, PartialEq)]
    pub struct Status: u8 {
        const Carry = 0b0000_0001;
        const Zero = 0b0000_0010;
        const Interrupt = 0b0000_0100;
        const Decimal = 0b0000_1000;
        const Break = 0b0001_0000;
        const Overflow = 0b0100_0000;
        const Negative = 0b1000_0000;
    }
}

#[derive(Derivative)]
#[derivative(Debug)]
pub struct CPU {
    register_a: u8,
    register_x: u8,
    register_y: u8,
    pub status: Status,
    pub program_counter: u16,
    pub stack_pointer: u8,

    #[derivative(Debug = "ignore")]
    memory: [u8; 0xFFFF],
}

impl Default for CPU {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Error, Debug)]
pub enum CPUError {
    #[error("Unknown instruction {0}")]
    UnknownOpcode(u8),

    #[error("IO Error")]
    IOError(#[from] std::io::Error),
}

impl CPU {
    pub fn new() -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: Status::empty(),
            program_counter: 0,
            stack_pointer: 0xFF,
            memory: [0; 0xFFFF],
        }
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
        loop {
            let instruction = self.read_u8();
            let opcode = OPCODE_MAP
                .get(&instruction)
                .ok_or(CPUError::UnknownOpcode(instruction))?;

            match opcode.mnemonic {
                Mnemonic::LDA => self.lda(&opcode.mode),
                Mnemonic::LDX => self.ldx(&opcode.mode),
                Mnemonic::LDY => self.ldy(&opcode.mode),
                Mnemonic::STA => self.sta(&opcode.mode),
                Mnemonic::AND => self.and(&opcode.mode),
                Mnemonic::ADC => self.adc(&opcode.mode),
                Mnemonic::ASL => self.asl(&opcode.mode),
                Mnemonic::TAX => self.tax(),
                Mnemonic::TAY => self.tay(),
                Mnemonic::TXA => self.txa(),
                Mnemonic::TYA => self.tya(),
                Mnemonic::INX => self.inx(),
                Mnemonic::INY => self.iny(),
                Mnemonic::BRK => break,
            }
        }

        Ok(())
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) -> Result<(), CPUError> {
        self.load(program);
        self.run()
    }

    pub fn load(&mut self, program: Vec<u8>) {
        self.memory[0x8000..0x8000 + program.len()].copy_from_slice(&program[..]);
        self.program_counter = 0x8000;
    }

    pub fn reset(&mut self) {
        self.register_x = 0;
        self.register_a = 0;
        self.program_counter = 0;
        self.status = Status::empty();

        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    fn mem_read_u8(&self, address: u16) -> u8 {
        self.memory[address as usize]
    }

    fn mem_write_u8(&mut self, address: u16, value: u8) {
        self.memory[address as usize] = value;
    }

    fn mem_read_u16(&self, address: u16) -> u16 {
        let hi = self.mem_read_u8(address);
        let lo = self.mem_read_u8(address + 1);

        u16::from_le_bytes([hi, lo])
    }

    fn mem_write_u16(&mut self, address: u16, value: u16) {
        let bytes = value.to_le_bytes();
        self.mem_write_u8(address, bytes[0]);
        self.mem_write_u8(address + 1, bytes[1]);
    }

    fn read_u8(&mut self) -> u8 {
        let result = self.mem_read_u8(self.program_counter);
        self.program_counter += 1;

        result
    }

    fn read_u16(&mut self) -> u16 {
        let hi = self.read_u8();
        let lo = self.read_u8();

        u16::from_le_bytes([hi, lo])
    }

    fn lda(&mut self, mode: &AddressMode) {
        let operand = self.get_operand(mode);
        self.set_register_a(operand);
    }

    fn ldx(&mut self, mode: &AddressMode) {
        let operand = self.get_operand(mode);
        self.set_register_x(operand);
    }

    fn ldy(&mut self, mode: &AddressMode) {
        let operand = self.get_operand(mode);
        self.set_register_y(operand);
    }

    fn sta(&mut self, mode: &AddressMode) {
        let address = self.get_operand_address(mode);
        self.mem_write_u8(address, self.register_a);
    }

    fn and(&mut self, mode: &AddressMode) {
        let operand = self.get_operand(mode);
        self.set_register_a(self.register_a & operand);
    }

    fn asl(&mut self, mode: &AddressMode) {
        let shift = |this: &mut Self, value: u8| {
            if value & 0x80 != 0 {
                this.status.insert(Status::Carry);
            } else {
                this.status.remove(Status::Carry);
            }

            value << 1
        };

        match mode {
            AddressMode::Accumulator => {
                let value = shift(self, self.register_a);
                self.set_register_a(value);
            }
            _ => {
                let address = self.get_operand_address(mode);
                let operand = self.mem_read_u8(address);
                let value = shift(self, operand);
                self.mem_write_u8(address, value);
                self.update_zero_and_negative_flags(value);
            }
        }
    }

    fn adc(&mut self, mode: &AddressMode) {
        let operand = self.get_operand(mode);
        let register_a = self.register_a as u16;
        let sum = register_a + operand as u16 + self.status.contains(Status::Carry) as u16;

        if sum > 0xFF {
            self.status.insert(Status::Carry);
        } else {
            self.status.remove(Status::Carry);
        }

        let result = sum as u8;
        if (result ^ operand) & (result ^ self.register_a) & 0x80 != 0 {
            self.status.insert(Status::Overflow);
        } else {
            self.status.remove(Status::Overflow);
        }

        self.set_register_a(sum as u8);
    }

    fn tax(&mut self) {
        self.set_register_x(self.register_a)
    }

    fn tay(&mut self) {
        self.set_register_y(self.register_a)
    }

    fn txa(&mut self) {
        self.set_register_a(self.register_x)
    }

    fn tya(&mut self) {
        self.set_register_a(self.register_y)
    }

    fn inx(&mut self) {
        self.set_register_x(self.register_x.wrapping_add(1));
    }
    fn iny(&mut self) {
        self.set_register_y(self.register_y.wrapping_add(1));
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

    fn update_zero_and_negative_flags(&mut self, result: u8) {
        self.update_zero_flag(result);
        self.update_negative_flag(result);
    }

    fn get_operand_address(&mut self, mode: &AddressMode) -> u16 {
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
            AddressMode::IndirectX => {
                let base = self.read_u8().wrapping_add(self.register_x);
                self.mem_read_u16(base as u16)
            }
            AddressMode::IndirectY => {
                let base = self.read_u8().wrapping_add(self.register_y);
                self.mem_read_u16(base as u16)
            }
            AddressMode::None => unreachable!(),
            AddressMode::Accumulator => unreachable!(),
        }
    }

    fn get_operand(&mut self, mode: &AddressMode) -> u8 {
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
        let program: Vec<u8> = vec![0x0A, 0x00];
        let mut cpu = CPU::new();
        cpu.register_a = 0x01;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x02);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn asl_accumulator_sets_carry() {
        let program: Vec<u8> = vec![0x0A, 0x00];
        let mut cpu = CPU::new();
        cpu.register_a = 0x81; // 10000001

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x02);
        assert_eq!(cpu.status, Status::Carry);
    }

    #[test]
    fn asl_accumulator_sets_zero() {
        let program: Vec<u8> = vec![0x0A, 0x00];
        let mut cpu = CPU::new();
        cpu.register_a = 0x00;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x00);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn asl_accumulator_sets_negative() {
        let program: Vec<u8> = vec![0x0A, 0x00];
        let mut cpu = CPU::new();
        cpu.register_a = 0x40; // Shift to get 10000000

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x80);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn asl_zeropage() {
        let program: Vec<u8> = vec![0x06, 0x10, 0x00];
        let mut cpu = CPU::new();
        cpu.mem_write_u8(0x10, 0x01);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.mem_read_u8(0x10), 0x02);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn asl_zeropage_x() {
        let program: Vec<u8> = vec![0x16, 0x10, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0x05;
        cpu.mem_write_u8(0x15, 0x01);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.mem_read_u8(0x15), 0x02);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn asl_absolute() {
        let program: Vec<u8> = vec![0x0E, 0x00, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.mem_write_u8(0x2000, 0x01);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.mem_read_u8(0x2000), 0x02);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn asl_absolute_x() {
        let program: Vec<u8> = vec![0x1E, 0x00, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0x05;
        cpu.mem_write_u8(0x2005, 0x01);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.mem_read_u8(0x2005), 0x02);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn asl_absolute_sets_carry_and_zero() {
        let program: Vec<u8> = vec![0x0E, 0x00, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.mem_write_u8(0x2000, 0x80); // 10000000 -> 00000000 with carry

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.mem_read_u8(0x2000), 0x00);
        assert_eq!(cpu.status, Status::Carry | Status::Zero);
    }

    #[test]
    fn lda_immediate() {
        let program: Vec<u8> = vec![0xa9, 0x05, 0x00];
        let mut cpu = CPU::new();

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 5);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn lda_immediate_zero() {
        let program: Vec<u8> = vec![0xa9, 0x00, 0x00];
        let mut cpu = CPU::new();

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn lda_zeropage() {
        let program: Vec<u8> = vec![0xa5, 0x05, 0x00];
        let mut cpu = CPU::new();
        cpu.mem_write_u8(0x05, 0x20);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn lda_zeropage_x() {
        let program: Vec<u8> = vec![0xb5, 0x05, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0x05;
        cpu.mem_write_u8(0x0a, 0x20);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn lda_absolute() {
        let program: Vec<u8> = vec![0xad, 0x05, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.mem_write_u8(0x2005, 0x20);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn lda_absolute_x() {
        let program: Vec<u8> = vec![0xbd, 0x05, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0x01;
        cpu.mem_write_u8(0x2006, 0x20);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn lda_absolute_y() {
        let program: Vec<u8> = vec![0xb9, 0x05, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.register_y = 0x01;
        cpu.mem_write_u8(0x2006, 0x20);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn lda_indirect_x() {
        let program: Vec<u8> = vec![0xa1, 0x05, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0x01;
        cpu.mem_write_u8(0x06, 0x20);
        cpu.mem_write_u8(0x07, 0x10);
        cpu.mem_write_u8(0x1020, 0x10);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x10);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn lda_indirect_y() {
        let program: Vec<u8> = vec![0xb1, 0x05, 0x00];
        let mut cpu = CPU::new();
        cpu.register_y = 0x01;
        cpu.mem_write_u8(0x06, 0x20);
        cpu.mem_write_u8(0x07, 0x10);
        cpu.mem_write_u8(0x1020, 0x10);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x10);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldx_immediate() {
        let program: Vec<u8> = vec![0xa2, 0x05, 0x00];
        let mut cpu = CPU::new();

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_x, 5);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldx_zeropage() {
        let program: Vec<u8> = vec![0xa6, 0x05, 0x00];
        let mut cpu = CPU::new();
        cpu.mem_write_u8(0x05, 0x20);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_x, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldx_zeropage_y() {
        let program: Vec<u8> = vec![0xb6, 0x05, 0x00];
        let mut cpu = CPU::new();
        cpu.register_y = 0x05;
        cpu.mem_write_u8(0x0a, 0x20);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_x, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldx_absolute() {
        let program: Vec<u8> = vec![0xae, 0x05, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.mem_write_u8(0x2005, 0x20);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_x, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldx_absolute_y() {
        let program: Vec<u8> = vec![0xbe, 0x05, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.register_y = 0x01;
        cpu.mem_write_u8(0x2006, 0x20);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_x, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldy_immediate() {
        let program: Vec<u8> = vec![0xa0, 0x05, 0x00];
        let mut cpu = CPU::new();

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_y, 5);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldy_zeropage() {
        let program: Vec<u8> = vec![0xa4, 0x05, 0x00];
        let mut cpu = CPU::new();
        cpu.mem_write_u8(0x05, 0x20);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_y, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldy_zeropage_x() {
        let program: Vec<u8> = vec![0xb4, 0x05, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0x05;
        cpu.mem_write_u8(0x0a, 0x20);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_y, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldy_absolute() {
        let program: Vec<u8> = vec![0xac, 0x05, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.mem_write_u8(0x2005, 0x20);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_y, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn ldy_absolute_x() {
        let program: Vec<u8> = vec![0xbc, 0x05, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0x01;
        cpu.mem_write_u8(0x2006, 0x20);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_y, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn and_immediate() {
        let program: Vec<u8> = vec![0x29, 0x10, 0x00];
        let mut cpu = CPU::new();
        cpu.register_a = 0xF0;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x10);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn and_zeropage() {
        let program: Vec<u8> = vec![0x25, 0x05, 0x00];
        let mut cpu = CPU::new();
        cpu.mem_write_u8(0x05, 0x20);
        cpu.register_a = 0xF0;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn and_zeropage_x() {
        let program: Vec<u8> = vec![0x35, 0x05, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0x05;
        cpu.register_a = 0xF0;
        cpu.mem_write_u8(0x0a, 0x20);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn and_absolute() {
        let program: Vec<u8> = vec![0xad, 0x05, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.mem_write_u8(0x2005, 0x20);
        cpu.register_a = 0xF0;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn and_absolute_x() {
        let program: Vec<u8> = vec![0x3d, 0x05, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0x01;
        cpu.mem_write_u8(0x2006, 0x20);
        cpu.register_a = 0xF0;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn and_absolute_y() {
        let program: Vec<u8> = vec![0x39, 0x05, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.register_y = 0x01;
        cpu.mem_write_u8(0x2006, 0x20);
        cpu.register_a = 0xF0;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn and_indirect_x() {
        let program: Vec<u8> = vec![0x21, 0x05, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0x01;
        cpu.register_a = 0xF0;
        cpu.mem_write_u8(0x06, 0x20);
        cpu.mem_write_u8(0x07, 0x10);
        cpu.mem_write_u8(0x1020, 0x10);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x10);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn and_indirect_y() {
        let program: Vec<u8> = vec![0x31, 0x05, 0x00];
        let mut cpu = CPU::new();
        cpu.register_y = 0x01;
        cpu.register_a = 0xF0;
        cpu.mem_write_u8(0x06, 0x20);
        cpu.mem_write_u8(0x07, 0x10);
        cpu.mem_write_u8(0x1020, 0x10);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x10);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn adc_immediate() {
        let program: Vec<u8> = vec![0x69, 0x10, 0x00];
        let mut cpu = CPU::new();
        cpu.register_a = 0x05;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x15);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn adc_immediate_with_carry() {
        let program: Vec<u8> = vec![0x69, 0x10, 0x00];
        let mut cpu = CPU::new();
        cpu.register_a = 0x05;
        cpu.status.insert(Status::Carry);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x16);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn adc_immediate_with_overflow() {
        let program: Vec<u8> = vec![0x69, 0x70, 0x00];
        let mut cpu = CPU::new();
        cpu.register_a = 0x50;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0xC0);
        assert_eq!(cpu.status, Status::Negative | Status::Overflow);
    }

    #[test]
    fn adc_immediate_with_carry_flag() {
        let program: Vec<u8> = vec![0x69, 0xFF, 0x00];
        let mut cpu = CPU::new();
        cpu.register_a = 0x01;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x00);
        assert_eq!(cpu.status, Status::Carry | Status::Zero);
    }

    #[test]
    fn adc_zeropage() {
        let program: Vec<u8> = vec![0x65, 0x05, 0x00];
        let mut cpu = CPU::new();
        cpu.mem_write_u8(0x05, 0x10);
        cpu.register_a = 0x05;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x15);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn adc_zeropage_x() {
        let program: Vec<u8> = vec![0x75, 0x05, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0x05;
        cpu.mem_write_u8(0x0A, 0x10);
        cpu.register_a = 0x05;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x15);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn adc_absolute() {
        let program: Vec<u8> = vec![0x6D, 0x05, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.mem_write_u8(0x2005, 0x10);
        cpu.register_a = 0x05;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x15);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn adc_absolute_x() {
        let program: Vec<u8> = vec![0x7D, 0x05, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0x01;
        cpu.mem_write_u8(0x2006, 0x10);
        cpu.register_a = 0x05;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x15);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn adc_absolute_y() {
        let program: Vec<u8> = vec![0x79, 0x05, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.register_y = 0x01;
        cpu.mem_write_u8(0x2006, 0x10);
        cpu.register_a = 0x05;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x15);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn adc_indirect_x() {
        let program: Vec<u8> = vec![0x61, 0x05, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0x01;
        cpu.register_a = 0x05;
        cpu.mem_write_u8(0x06, 0x20);
        cpu.mem_write_u8(0x07, 0x10);
        cpu.mem_write_u8(0x1020, 0x10);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x15);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn adc_indirect_y() {
        let program: Vec<u8> = vec![0x71, 0x05, 0x00];
        let mut cpu = CPU::new();
        cpu.register_y = 0x01;
        cpu.register_a = 0x05;
        cpu.mem_write_u8(0x06, 0x20);
        cpu.mem_write_u8(0x07, 0x10);
        cpu.mem_write_u8(0x1020, 0x10);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x15);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn sta_zeropage() {
        let program: Vec<u8> = vec![0x85, 0x12, 0x00];
        let mut cpu = CPU::new();
        cpu.register_a = 0x20;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.mem_read_u8(0x12), 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn sta_zeropage_x() {
        let program: Vec<u8> = vec![0x95, 0x12, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0x05;
        cpu.register_a = 0x20;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.mem_read_u8(0x17), 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn sta_absolute() {
        let program: Vec<u8> = vec![0x8d, 0x05, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.register_a = 0x20;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.mem_read_u8(0x2005), 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn sta_absolute_x() {
        let program: Vec<u8> = vec![0x9d, 0x05, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0x01;
        cpu.register_a = 0x20;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.mem_read_u8(0x2006), 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn sta_absolute_y() {
        let program: Vec<u8> = vec![0x99, 0x05, 0x20, 0x00];
        let mut cpu = CPU::new();
        cpu.register_y = 0x01;
        cpu.register_a = 0x20;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.mem_read_u8(0x2006), 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn sta_indirect_x() {
        let program: Vec<u8> = vec![0x81, 0x05, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0x01;
        cpu.register_a = 0x20;
        cpu.mem_write_u16(0x06, 0x2006);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.mem_read_u8(0x2006), 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn sta_indirect_y() {
        let program: Vec<u8> = vec![0x91, 0x05, 0x00];
        let mut cpu = CPU::new();
        cpu.register_y = 0x01;
        cpu.register_a = 0x20;
        cpu.mem_write_u16(0x06, 0x2006);

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.mem_read_u8(0x2006), 0x20);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn tax() {
        let program: Vec<u8> = vec![0xaa, 0x00];
        let mut cpu = CPU::new();
        cpu.register_a = 10;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_x, 10);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn tax_zero_flag() {
        let program: Vec<u8> = vec![0xaa, 0x00];
        let mut cpu = CPU::new();
        cpu.register_a = 0;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_x, 0);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn tax_negative_flag() {
        let program: Vec<u8> = vec![0xaa, 0x00];
        let mut cpu = CPU::new();
        cpu.register_a = 0x80;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_x, 0x80);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn tay() {
        let program: Vec<u8> = vec![0xa8, 0x00];
        let mut cpu = CPU::new();
        cpu.register_a = 10;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_y, 10);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn tay_zero_flag() {
        let program: Vec<u8> = vec![0xa8, 0x00];
        let mut cpu = CPU::new();
        cpu.register_a = 0;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_y, 0);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn tay_negative_flag() {
        let program: Vec<u8> = vec![0xa8, 0x00];
        let mut cpu = CPU::new();
        cpu.register_a = 0x80;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_y, 0x80);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn txa() {
        let program: Vec<u8> = vec![0x8a, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 10;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 10);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn txa_zero_flag() {
        let program: Vec<u8> = vec![0x8a, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn txa_negative_flag() {
        let program: Vec<u8> = vec![0x8a, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0x80;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x80);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn tya() {
        let program: Vec<u8> = vec![0x98, 0x00];
        let mut cpu = CPU::new();
        cpu.register_y = 10;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 10);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn tya_zero_flag() {
        let program: Vec<u8> = vec![0x98, 0x00];
        let mut cpu = CPU::new();
        cpu.register_y = 0;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0);
        assert_eq!(cpu.status, Status::Zero);
    }

    #[test]
    fn tya_negative_flag() {
        let program: Vec<u8> = vec![0x98, 0x00];
        let mut cpu = CPU::new();
        cpu.register_y = 0x80;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_a, 0x80);
        assert_eq!(cpu.status, Status::Negative);
    }

    #[test]
    fn inx() {
        let program: Vec<u8> = vec![0xe8, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 5;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_x, 6);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn inx_overflow() {
        let program: Vec<u8> = vec![0xe8, 0x00];
        let mut cpu = CPU::new();
        cpu.register_x = 0xff;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_x, 0x00);
        assert_eq!(cpu.status, Status::Zero);
    }
    #[test]
    fn iny() {
        let program: Vec<u8> = vec![0xc8, 0x00];
        let mut cpu = CPU::new();
        cpu.register_y = 5;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_y, 6);
        assert!(cpu.status.is_empty());
    }

    #[test]
    fn iny_overflow() {
        let program: Vec<u8> = vec![0xc8, 0x00];
        let mut cpu = CPU::new();
        cpu.register_y = 0xff;

        if let Err(err) = cpu.load_and_run(program) {
            unreachable!("{}", err);
        }

        assert_eq!(cpu.register_y, 0x00);
        assert_eq!(cpu.status, Status::Zero);
    }
}
