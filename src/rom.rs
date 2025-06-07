use std::io::Cursor;

use byteorder::{BigEndian, ReadBytesExt};
use thiserror::Error;

const MAGIC_BYTES: [u8; 4] = [0x4E, 0x45, 0x53, 0x1A];
const PROGRAM_ROM_PAGE_SIZE: usize = 16 * 1024;
const CHARACTER_ROM_PAGE_SIZE: usize = 8 * 1024;

#[derive(Debug)]
pub enum Mirroring {
    VERTICAL,
    HORIZONTAL,
    FOURSCREEN,
}

impl Default for Mirroring {
    fn default() -> Self {
        Mirroring::VERTICAL
    }
}

#[derive(Debug, Default)]
pub struct ROM {
    pub program: Vec<u8>,
    pub character: Vec<u8>,
    pub mapper: u8,
    pub mirroring: Mirroring,
}

#[derive(Debug, Error)]
pub enum ROMError {
    #[error("Invalid ROM")]
    InvalidROM,

    #[error("Unsupported NES version")]
    UnsupportedVersion,

    #[error("IO Error")]
    IOError(#[from] std::io::Error),
}

impl ROM {
    pub fn new(program: Vec<u8>, character: Vec<u8>, mapper: u8, mirroring: Mirroring) -> Self {
        ROM {
            program,
            character,
            mapper,
            mirroring,
        }
    }

    pub fn read_program_rom(&self, address: u16) -> u8 {
        let mut addr = address - 0x8000;
        if self.program.len() == 0x4000 && addr >= 0x4000 {
            addr %= 0x4000;
        }
        self.program[addr as usize]
    }

    // source: https://formats.kaitai.io/ines/index.html
    pub fn from_bytes(raw: &Vec<u8>) -> Result<ROM, ROMError> {
        let mut cursor = Cursor::new(raw);

        let magic_bytes = cursor.read_u32::<BigEndian>()?;
        if magic_bytes != u32::from_be_bytes(MAGIC_BYTES) {
            return Err(ROMError::InvalidROM);
        }

        let program_rom_size = cursor.read_u8()? as usize * PROGRAM_ROM_PAGE_SIZE;
        let character_rom_size = cursor.read_u8()? as usize * CHARACTER_ROM_PAGE_SIZE;

        let f6 = cursor.read_u8()?;
        let lower_mapper = f6 >> 4;
        let four_screen = (f6 >> 3) & 1;
        let trainer = (f6 >> 2) & 1;
        // let has_battery_ram = (f6 >> 1) & 1;
        let mirroring = f6 & 1;

        let f7 = cursor.read_u8()?;
        let upper_mapper = f7 >> 4;
        let format = (f7 >> 2) & 0b11;
        if format != 0 {
            return Err(ROMError::UnsupportedVersion);
        }

        // let play_choice = (f7 >> 1) & 1;
        // let vs_unisystem = f7 & 1;

        let mut trainer_offset = 0;
        if trainer != 0 {
            trainer_offset = 512;
        }

        let program_rom_start = 16 + trainer_offset;
        let character_rom_start = program_rom_start + program_rom_size;
        let character_rom_end = character_rom_start + character_rom_size;

        let mirroring = match (four_screen != 0, mirroring != 0) {
            (true, _) => Mirroring::FOURSCREEN,
            (false, true) => Mirroring::VERTICAL,
            (false, false) => Mirroring::HORIZONTAL,
        };

        let rom = ROM::new(
            raw[program_rom_start..character_rom_start].to_vec(),
            raw[character_rom_start..character_rom_end].to_vec(),
            lower_mapper | (upper_mapper << 4),
            mirroring,
        );

        Ok(rom)
    }
}
