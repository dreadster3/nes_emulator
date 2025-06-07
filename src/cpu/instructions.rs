use super::opcodes::AddressMode;

use super::{CPU, Status, memory::Memory};

pub(super) trait LoadStoreOperations {
    fn lda(&mut self, mode: &AddressMode);
    fn ldx(&mut self, mode: &AddressMode);
    fn ldy(&mut self, mode: &AddressMode);
    fn sta(&mut self, mode: &AddressMode);
}

impl LoadStoreOperations for CPU {
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
        self.mem_write_u8(address, self.get_register_a());
    }
}

pub(super) trait RegisterTransferOperations {
    fn tax(&mut self);
    fn tay(&mut self);
    fn txa(&mut self);
    fn tya(&mut self);
    fn tsx(&mut self);
    fn txs(&mut self);
}

impl RegisterTransferOperations for CPU {
    fn tax(&mut self) {
        self.set_register_x(self.get_register_a());
    }

    fn tay(&mut self) {
        self.set_register_y(self.get_register_a());
    }

    fn txa(&mut self) {
        self.set_register_a(self.get_register_x());
    }

    fn tya(&mut self) {
        self.set_register_a(self.get_register_y());
    }

    fn tsx(&mut self) {
        self.set_register_x(self.get_stack_pointer());
    }

    fn txs(&mut self) {
        self.set_stack_pointer(self.get_register_x());
    }
}

pub(super) trait ArithmeticOperations {
    fn compare(&mut self, left: u8, right: u8);
    fn add_register_a(&mut self, value: u8);

    fn adc(&mut self, mode: &AddressMode);
    fn cmp(&mut self, mode: &AddressMode);
    fn sbc(&mut self, mode: &AddressMode);
    fn cpx(&mut self, mode: &AddressMode);
    fn cpy(&mut self, mode: &AddressMode);
}

impl ArithmeticOperations for CPU {
    fn compare(&mut self, left: u8, right: u8) {
        if left >= right {
            self.status.insert(Status::Carry);
            if left == right {
                self.status.insert(Status::Zero);
            } else {
                self.status.remove(Status::Zero);
            }
        } else {
            self.status.remove(Status::Zero);
            self.status.remove(Status::Carry);
        }
    }

    fn add_register_a(&mut self, value: u8) {
        let register_a = self.register_a as u16;
        let sum = register_a + value as u16 + self.status.contains(Status::Carry) as u16;

        if sum > 0xFF {
            self.status.insert(Status::Carry);
        } else {
            self.status.remove(Status::Carry);
        }

        let result = sum as u8;
        if (result ^ value) & (result ^ self.register_a) & 0x80 != 0 {
            self.status.insert(Status::Overflow);
        } else {
            self.status.remove(Status::Overflow);
        }

        self.set_register_a(sum as u8);
    }

    fn adc(&mut self, mode: &AddressMode) {
        let operand = self.get_operand(mode);
        self.add_register_a(operand);
    }

    fn cmp(&mut self, mode: &AddressMode) {
        let register_a = self.register_a;
        let operand = self.get_operand(mode);
        self.compare(register_a, operand);
    }

    fn cpx(&mut self, mode: &AddressMode) {
        let register_x = self.register_x;
        let operand = self.get_operand(mode);
        self.compare(register_x, operand);
    }

    fn cpy(&mut self, mode: &AddressMode) {
        let register_y = self.register_y;
        let operand = self.get_operand(mode);
        self.compare(register_y, operand);
    }

    fn sbc(&mut self, mode: &AddressMode) {
        let operand = self.get_operand(mode);
        self.add_register_a(!operand);
    }
}

pub(super) trait StackOperations {
    fn pha(&mut self);
    fn pla(&mut self);
    fn php(&mut self);
    fn plp(&mut self);
}

impl StackOperations for CPU {
    fn pha(&mut self) {
        self.stack_push(self.get_register_a());
    }

    fn pla(&mut self) {
        let data = self.stack_pop();
        self.set_register_a(data);
    }

    fn php(&mut self) {
        self.stack_push(self.status.bits());
    }

    fn plp(&mut self) {
        self.status = Status::from_bits_truncate(self.stack_pop());
    }
}

pub(super) trait LogicalOperations {
    fn and(&mut self, mode: &AddressMode);
    fn ora(&mut self, mode: &AddressMode);
    fn eor(&mut self, mode: &AddressMode);
}

impl LogicalOperations for CPU {
    fn and(&mut self, mode: &AddressMode) {
        let operand = self.get_operand(mode);
        self.set_register_a(self.get_register_a() & operand);
    }

    fn ora(&mut self, mode: &AddressMode) {
        let operand = self.get_operand(mode);
        self.set_register_a(self.get_register_a() | operand);
    }

    fn eor(&mut self, mode: &AddressMode) {
        let operand = self.get_operand(mode);
        self.set_register_a(self.get_register_a() ^ operand);
    }
}

pub(super) trait IncrementOperations {
    fn inx(&mut self);
    fn iny(&mut self);
    fn inc(&mut self, mode: &AddressMode);
}

impl IncrementOperations for CPU {
    fn inx(&mut self) {
        self.set_register_x(self.get_register_x().wrapping_add(1));
    }

    fn iny(&mut self) {
        self.set_register_y(self.get_register_y().wrapping_add(1));
    }

    fn inc(&mut self, mode: &AddressMode) {
        let address = self.get_operand_address(mode);
        let value = self.mem_read_u8(address);
        let result = value.wrapping_add(1);
        self.mem_write_u8(address, result);
        self.update_zero_and_negative_flags(result);
    }
}

pub(super) trait DecrementOperations {
    fn dex(&mut self);
    fn dey(&mut self);
    fn dec(&mut self, mode: &AddressMode);
}

impl DecrementOperations for CPU {
    fn dex(&mut self) {
        self.set_register_x(self.get_register_x().wrapping_sub(1));
    }

    fn dey(&mut self) {
        self.set_register_y(self.get_register_y().wrapping_sub(1));
    }

    fn dec(&mut self, mode: &AddressMode) {
        let address = self.get_operand_address(mode);
        let value = self.mem_read_u8(address);
        let result = value.wrapping_sub(1);
        self.mem_write_u8(address, result);
        self.update_zero_and_negative_flags(result);
    }
}

pub(super) trait JumpOperations {
    fn jmp(&mut self, mode: &AddressMode);
    fn jsr(&mut self, mode: &AddressMode);
    fn rts(&mut self);
    fn rti(&mut self);
}

impl JumpOperations for CPU {
    fn jmp(&mut self, mode: &AddressMode) {
        let address = self.get_operand_address(mode);
        self.program_counter = address;
    }

    fn jsr(&mut self, mode: &AddressMode) {
        let target_address = self.get_operand_address(mode);
        self.stack_push_u16(self.program_counter - 1);
        self.program_counter = target_address;
    }

    fn rts(&mut self) {
        self.program_counter = self.stack_pop_u16() + 1;
    }

    fn rti(&mut self) {
        self.status = Status::from_bits_truncate(self.stack_pop());
        self.program_counter = self.stack_pop_u16();
    }
}

pub(super) trait BitwiseTestOperations {
    fn bit(&mut self, mode: &AddressMode);
}

impl BitwiseTestOperations for CPU {
    fn bit(&mut self, mode: &AddressMode) {
        let operand = self.get_operand(mode);
        let result = self.register_a & operand;

        // Set Zero flag based on result
        if result == 0 {
            self.status.insert(Status::Zero);
        } else {
            self.status.remove(Status::Zero);
        }

        // Set Negative flag to bit 7 of operand
        if operand & 0x80 != 0 {
            self.status.insert(Status::Negative);
        } else {
            self.status.remove(Status::Negative);
        }

        // Set Overflow flag to bit 6 of operand
        if operand & 0x40 != 0 {
            self.status.insert(Status::Overflow);
        } else {
            self.status.remove(Status::Overflow);
        }
    }
}

pub(super) trait StatusFlagsOperations {
    fn clc(&mut self);
    fn cli(&mut self);
    fn clv(&mut self);
    fn cld(&mut self);
    fn sec(&mut self);
    fn sei(&mut self);
    fn sed(&mut self);
}

impl StatusFlagsOperations for CPU {
    fn clc(&mut self) {
        self.status.remove(Status::Carry);
    }

    fn cli(&mut self) {
        self.status.remove(Status::InterruptDisable);
    }

    fn clv(&mut self) {
        self.status.remove(Status::Overflow);
    }

    fn cld(&mut self) {
        self.status.remove(Status::Decimal);
    }

    fn sec(&mut self) {
        self.status.insert(Status::Carry);
    }

    fn sei(&mut self) {
        self.status.insert(Status::InterruptDisable);
    }

    fn sed(&mut self) {
        self.status.insert(Status::Decimal);
    }
}

pub(super) trait BranchOperations {
    fn branch(&mut self, condition: bool);
    fn status(&self) -> &Status;

    fn bcc(&mut self) {
        self.branch(!self.status().contains(Status::Carry));
    }
    fn bcs(&mut self) {
        self.branch(self.status().contains(Status::Carry));
    }
    fn beq(&mut self) {
        self.branch(self.status().contains(Status::Zero));
    }
    fn bmi(&mut self) {
        self.branch(self.status().contains(Status::Negative));
    }
    fn bne(&mut self) {
        self.branch(!self.status().contains(Status::Zero));
    }
    fn bpl(&mut self) {
        self.branch(!self.status().contains(Status::Negative));
    }
    fn bvc(&mut self) {
        self.branch(!self.status().contains(Status::Overflow));
    }
    fn bvs(&mut self) {
        self.branch(self.status().contains(Status::Overflow));
    }
}

impl BranchOperations for CPU {
    fn branch(&mut self, condition: bool) {
        let offset = self.read_u8() as i8;
        if condition {
            let address = self.program_counter.wrapping_add(offset as u16);
            self.program_counter = address;
        }
    }

    fn status(&self) -> &Status {
        &self.status
    }
}

pub(super) trait ShiftOperations {
    fn shift_left(&mut self, value: u8) -> u8;
    fn shift_right(&mut self, value: u8) -> u8;

    fn asl(&mut self, mode: &AddressMode);
    fn lsr(&mut self, mode: &AddressMode);
    fn rol(&mut self, mode: &AddressMode);
    fn ror(&mut self, mode: &AddressMode);
}

impl ShiftOperations for CPU {
    fn shift_left(&mut self, value: u8) -> u8 {
        if value & 0x80 != 0 {
            self.status.insert(Status::Carry);
        } else {
            self.status.remove(Status::Carry);
        }

        value << 1
    }

    fn shift_right(&mut self, value: u8) -> u8 {
        if value & 1 != 0 {
            self.status.insert(Status::Carry);
        } else {
            self.status.remove(Status::Carry);
        }

        value >> 1
    }

    fn asl(&mut self, mode: &AddressMode) {
        match mode {
            AddressMode::Accumulator => {
                let value = self.shift_left(self.register_a);
                self.set_register_a(value);
            }
            _ => {
                let address = self.get_operand_address(mode);
                let operand = self.mem_read_u8(address);
                let value = self.shift_left(operand);
                self.mem_write_u8(address, value);
                self.update_zero_and_negative_flags(value);
            }
        }
    }

    fn lsr(&mut self, mode: &AddressMode) {
        match mode {
            AddressMode::Accumulator => {
                let value = self.shift_right(self.register_a);
                self.set_register_a(value);
            }
            _ => {
                let address = self.get_operand_address(mode);
                let operand = self.mem_read_u8(address);
                let value = self.shift_right(operand);
                self.mem_write_u8(address, value);
                self.update_zero_and_negative_flags(value);
            }
        }
    }

    fn rol(&mut self, mode: &AddressMode) {
        let old_carry = self.status.contains(Status::Carry) as u8;

        match mode {
            AddressMode::Accumulator => {
                let value = self.shift_left(self.register_a) | old_carry;
                self.set_register_a(value);
            }
            _ => {
                let address = self.get_operand_address(mode);
                let operand = self.mem_read_u8(address);
                let value = self.shift_left(operand) | old_carry;
                self.mem_write_u8(address, value);
                self.update_zero_and_negative_flags(value);
            }
        }
    }

    fn ror(&mut self, mode: &AddressMode) {
        let old_carry = self.status.contains(Status::Carry) as u8;

        match mode {
            AddressMode::Accumulator => {
                let value = self.shift_right(self.register_a) | (old_carry << 7);
                self.set_register_a(value);
            }
            _ => {
                let address = self.get_operand_address(mode);
                let operand = self.mem_read_u8(address);
                let value = self.shift_right(operand) | (old_carry << 7);
                self.mem_write_u8(address, value);
                self.update_zero_and_negative_flags(value);
            }
        }
    }
}
