use lazy_static::lazy_static;
use std::collections::HashMap;

pub enum AddressMode {
    Accumulator,
    Immediate,
    ZeroPage,
    ZeroPageX,
    ZeroPageY,
    Absolute,
    AbsoluteX,
    AbsoluteY,
    IndirectX,
    IndirectY,
    None,
}

pub enum Mnemonic {
    // Load/Store
    LDA,
    LDY,
    LDX,
    STA,

    // Register Transfer
    TAX,
    TAY,
    TXA,
    TYA,

    // Increment/Decrement
    INX,
    INY,
    INC,
    DEX,
    DEY,
    DEC,

    // Arithmetic
    ADC,

    // Logical
    AND,

    // Shift
    ASL,

    // Other
    BRK,
    NOP,
}

pub struct OpCode {
    pub code: u8,
    pub mnemonic: Mnemonic,
    pub len: u8,
    pub cycles: u8,
    pub mode: AddressMode,
}

impl OpCode {
    fn new(code: u8, mnemonic: Mnemonic, len: u8, cycles: u8, mode: AddressMode) -> Self {
        OpCode {
            code,
            mnemonic,
            len,
            cycles,
            mode,
        }
    }
}

lazy_static! {
    pub static ref OPCODES: Vec<OpCode> = vec![
        OpCode::new(0x00, Mnemonic::BRK, 1, 7, AddressMode::None),
        OpCode::new(0xea, Mnemonic::NOP, 1, 2, AddressMode::None),
        OpCode::new(0xaa, Mnemonic::TAX, 1, 2, AddressMode::None),
        OpCode::new(0xa8, Mnemonic::TAY, 1, 2, AddressMode::None),
        OpCode::new(0x8a, Mnemonic::TXA, 1, 2, AddressMode::None),
        OpCode::new(0x98, Mnemonic::TYA, 1, 2, AddressMode::None),
        OpCode::new(0xe8, Mnemonic::INX, 1, 2, AddressMode::None),
        OpCode::new(0xc8, Mnemonic::INY, 1, 2, AddressMode::None),
        OpCode::new(0xca, Mnemonic::DEX, 1, 2, AddressMode::None),
        OpCode::new(0x88, Mnemonic::DEY, 1, 2, AddressMode::None),

        // LDA
        OpCode::new(0xa9, Mnemonic::LDA, 2, 2, AddressMode::Immediate),
        OpCode::new(0xa5, Mnemonic::LDA, 2, 3, AddressMode::ZeroPage),
        OpCode::new(0xb5, Mnemonic::LDA, 2, 4, AddressMode::ZeroPageX),
        OpCode::new(0xad, Mnemonic::LDA, 3, 4, AddressMode::Absolute),
        OpCode::new(0xbd, Mnemonic::LDA, 3, 4, AddressMode::AbsoluteX),
        OpCode::new(0xb9, Mnemonic::LDA, 3, 4, AddressMode::AbsoluteY),
        OpCode::new(0xa1, Mnemonic::LDA, 2, 6, AddressMode::IndirectX),
        OpCode::new(0xb1, Mnemonic::LDA, 2, 5, AddressMode::IndirectY),

        // LDX
        OpCode::new(0xa2, Mnemonic::LDX, 2, 2, AddressMode::Immediate),
        OpCode::new(0xa6, Mnemonic::LDX, 2, 3, AddressMode::ZeroPage),
        OpCode::new(0xb6, Mnemonic::LDX, 2, 4, AddressMode::ZeroPageY),
        OpCode::new(0xae, Mnemonic::LDX, 3, 4, AddressMode::Absolute),
        OpCode::new(0xbe, Mnemonic::LDX, 3, 4, AddressMode::AbsoluteY),

        // LDY
        OpCode::new(0xa0, Mnemonic::LDY, 2, 2, AddressMode::Immediate),
        OpCode::new(0xa4, Mnemonic::LDY, 2, 3, AddressMode::ZeroPage),
        OpCode::new(0xb4, Mnemonic::LDY, 2, 4, AddressMode::ZeroPageX),
        OpCode::new(0xac, Mnemonic::LDY, 3, 4, AddressMode::Absolute),
        OpCode::new(0xbc, Mnemonic::LDY, 3, 4, AddressMode::AbsoluteX),

        // STA
        OpCode::new(0x85, Mnemonic::STA, 2, 2, AddressMode::ZeroPage),
        OpCode::new(0x95, Mnemonic::STA, 2, 4, AddressMode::ZeroPageX),
        OpCode::new(0x8d, Mnemonic::STA, 3, 4, AddressMode::Absolute),
        OpCode::new(0x9d, Mnemonic::STA, 3, 5, AddressMode::AbsoluteX),
        OpCode::new(0x99, Mnemonic::STA, 3, 5, AddressMode::AbsoluteY),
        OpCode::new(0x81, Mnemonic::STA, 2, 6, AddressMode::IndirectX),
        OpCode::new(0x91, Mnemonic::STA, 2, 6, AddressMode::IndirectY),

        // AND
        OpCode::new(0x29, Mnemonic::AND, 2, 2, AddressMode::Immediate),
        OpCode::new(0x25, Mnemonic::AND, 2, 3, AddressMode::ZeroPage),
        OpCode::new(0x35, Mnemonic::AND, 2, 4, AddressMode::ZeroPageX),
        OpCode::new(0x2d, Mnemonic::AND, 3, 4, AddressMode::Absolute),
        OpCode::new(0x3d, Mnemonic::AND, 3, 4, AddressMode::AbsoluteX),
        OpCode::new(0x39, Mnemonic::AND, 3, 4, AddressMode::AbsoluteY),
        OpCode::new(0x21, Mnemonic::AND, 2, 6, AddressMode::IndirectX),
        OpCode::new(0x31, Mnemonic::AND, 2, 5, AddressMode::IndirectY),

        // ADC
        OpCode::new(0x69, Mnemonic::ADC, 2, 2, AddressMode::Immediate),
        OpCode::new(0x65, Mnemonic::ADC, 2, 3, AddressMode::ZeroPage),
        OpCode::new(0x75, Mnemonic::ADC, 2, 4, AddressMode::ZeroPageX),
        OpCode::new(0x6d, Mnemonic::ADC, 3, 4, AddressMode::Absolute),
        OpCode::new(0x7d, Mnemonic::ADC, 3, 4, AddressMode::AbsoluteX),
        OpCode::new(0x79, Mnemonic::ADC, 3, 4, AddressMode::AbsoluteY),
        OpCode::new(0x61, Mnemonic::ADC, 2, 6, AddressMode::IndirectX),
        OpCode::new(0x71, Mnemonic::ADC, 2, 5, AddressMode::IndirectY),

        // ASL
        OpCode::new(0x0A, Mnemonic::ASL, 1, 2, AddressMode::Accumulator),
        OpCode::new(0x06, Mnemonic::ASL, 2, 5, AddressMode::ZeroPage),
        OpCode::new(0x16, Mnemonic::ASL, 2, 6, AddressMode::ZeroPageX),
        OpCode::new(0x0E, Mnemonic::ASL, 3, 6, AddressMode::Absolute),
        OpCode::new(0x1E, Mnemonic::ASL, 3, 7, AddressMode::AbsoluteX),

        // INC
        OpCode::new(0xE6, Mnemonic::INC, 2, 5, AddressMode::ZeroPage),
        OpCode::new(0xF6, Mnemonic::INC, 2, 6, AddressMode::ZeroPageX),
        OpCode::new(0xEE, Mnemonic::INC, 3, 6, AddressMode::Absolute),
        OpCode::new(0xFE, Mnemonic::INC, 3, 7, AddressMode::AbsoluteX),

        // DEC
        OpCode::new(0xC6, Mnemonic::DEC, 2, 5, AddressMode::ZeroPage),
        OpCode::new(0xD6, Mnemonic::DEC, 2, 6, AddressMode::ZeroPageX),
        OpCode::new(0xCE, Mnemonic::DEC, 3, 6, AddressMode::Absolute),
        OpCode::new(0xDE, Mnemonic::DEC, 3, 7, AddressMode::AbsoluteX),
    ];

    pub static ref OPCODE_MAP: HashMap<u8, &'static OpCode> = OPCODES.iter().fold(HashMap::new(), |mut map, opcode| {
        map.insert(opcode.code, opcode);
        map
    });
}
