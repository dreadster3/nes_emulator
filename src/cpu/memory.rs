use crate::cpu::CPU;

pub trait Memory {
    fn mem_read_u8(&self, address: u16) -> u8;
    fn mem_write_u8(&mut self, address: u16, value: u8);
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
}

impl Memory for CPU {
    fn mem_read_u8(&self, address: u16) -> u8 {
        self.bus.mem_read_u8(address)
    }

    fn mem_write_u8(&mut self, address: u16, value: u8) {
        self.bus.mem_write_u8(address, value);
    }
}
