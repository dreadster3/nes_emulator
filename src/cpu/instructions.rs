use crate::opcodes::AddressMode;

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

pub(super) trait ArithmeticOperations {}
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
