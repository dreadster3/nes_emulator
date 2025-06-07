use derivative::Derivative;

use super::memory::Memory;

const RAM_START: u16 = 0x0000;
const RAM_END: u16 = 0x1FFF;
const RAM_SIZE_ADDRESSES: usize = ((RAM_END - RAM_START + 1) / 4) as usize;
const PPU_START: u16 = 0x2000;
const PPU_END: u16 = 0x3FFF;
const PPU_SIZE_ADDRESSES: usize = ((PPU_END - PPU_START + 1) / 4) as usize;

enum AddressType {
    RAM(u16),
    PPU(u16),
    Unknown(u16),
}

#[derive(Derivative)]
#[derivative(Debug)]
pub struct Bus {
    #[derivative(Debug = "ignore")]
    vram: [u8; RAM_SIZE_ADDRESSES],
}

impl Default for Bus {
    fn default() -> Self {
        Self::new()
    }
}

impl Bus {
    pub fn new() -> Self {
        Bus {
            vram: [0; RAM_SIZE_ADDRESSES],
        }
    }

    fn normalize_address(address: u16) -> AddressType {
        match address {
            RAM_START..=RAM_END => AddressType::RAM(address & 0b111_1111_1111),
            PPU_START..=PPU_END => AddressType::PPU(address & 0b10_0000_0000_0111),
            _ => AddressType::Unknown(address),
        }
    }
}

impl Memory for Bus {
    fn mem_write_u8(&mut self, address: u16, value: u8) {
        let normalized = Bus::normalize_address(address);

        match normalized {
            AddressType::RAM(add) => {
                self.vram[add as usize] = value;
            }
            AddressType::PPU(add) => {
                todo!("PPU not supported")
            }
            AddressType::Unknown(add) => {
                println!("Unknown address: {:#04x}", add);
            }
        }
    }

    fn mem_read_u8(&self, address: u16) -> u8 {
        let normalized = Bus::normalize_address(address);

        match normalized {
            AddressType::RAM(add) => self.vram[add as usize],
            AddressType::PPU(add) => todo!("PPU not supported"),
            AddressType::Unknown(add) => {
                eprintln!("Unknown address: {:#04x}", add);
                0
            }
        }
    }
}
