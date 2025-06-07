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
    Indirect,
    IndirectX,
    IndirectY,
    Relative,
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
    TXS,
    TSX,

    // Stack operations
    PHA,
    PHP,
    PLA,
    PLP,

    // Increment/Decrement
    INX,
    INY,
    INC,
    DEX,
    DEY,
    DEC,

    // Jumps
    JSR,
    JMP,
    RTI,
    RTS,

    // Branches
    BEQ,
    BNE,
    BCS,
    BCC,
    BMI,
    BPL,
    BVS,
    BVC,

    // Arithmetic
    ADC,
    SBC,
    CMP,
    CPX,
    CPY,

    // Logical
    AND,
    EOR,
    ORA,

    // Shift
    ASL,
    LSR,
    ROL,
    ROR,

    // Flags
    CLC,
    CLD,
    CLI,
    CLV,
    SEC,
    SED,
    SEI,

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
        OpCode::new(0xba, Mnemonic::TSX, 1, 2, AddressMode::None),
        OpCode::new(0x9a, Mnemonic::TXS, 1, 2, AddressMode::None),
        OpCode::new(0xe8, Mnemonic::INX, 1, 2, AddressMode::None),
        OpCode::new(0xc8, Mnemonic::INY, 1, 2, AddressMode::None),
        OpCode::new(0xca, Mnemonic::DEX, 1, 2, AddressMode::None),
        OpCode::new(0x88, Mnemonic::DEY, 1, 2, AddressMode::None),
        OpCode::new(0x48, Mnemonic::PHA, 1, 3, AddressMode::None),
        OpCode::new(0x68, Mnemonic::PLA, 1, 4, AddressMode::None),
        OpCode::new(0x08, Mnemonic::PHP, 1, 3, AddressMode::None),
        OpCode::new(0x28, Mnemonic::PLP, 1, 4, AddressMode::None),


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

        // EOR
        OpCode::new(0x49, Mnemonic::EOR, 2, 2, AddressMode::Immediate),
        OpCode::new(0x45, Mnemonic::EOR, 2, 3, AddressMode::ZeroPage),
        OpCode::new(0x55, Mnemonic::EOR, 2, 4, AddressMode::ZeroPageX),
        OpCode::new(0x4d, Mnemonic::EOR, 3, 4, AddressMode::Absolute),
        OpCode::new(0x5d, Mnemonic::EOR, 3, 4, AddressMode::AbsoluteX),
        OpCode::new(0x59, Mnemonic::EOR, 3, 4, AddressMode::AbsoluteY),
        OpCode::new(0x41, Mnemonic::EOR, 2, 6, AddressMode::IndirectX),
        OpCode::new(0x51, Mnemonic::EOR, 2, 5, AddressMode::IndirectY),

        // ORA
        OpCode::new(0x09, Mnemonic::ORA, 2, 2, AddressMode::Immediate),
        OpCode::new(0x05, Mnemonic::ORA, 2, 3, AddressMode::ZeroPage),
        OpCode::new(0x15, Mnemonic::ORA, 2, 4, AddressMode::ZeroPageX),
        OpCode::new(0x0d, Mnemonic::ORA, 3, 4, AddressMode::Absolute),
        OpCode::new(0x1d, Mnemonic::ORA, 3, 4, AddressMode::AbsoluteX),
        OpCode::new(0x19, Mnemonic::ORA, 3, 4, AddressMode::AbsoluteY),
        OpCode::new(0x01, Mnemonic::ORA, 2, 6, AddressMode::IndirectX),
        OpCode::new(0x11, Mnemonic::ORA, 2, 5, AddressMode::IndirectY),


        // Shifts
        //// ASL
        OpCode::new(0x0A, Mnemonic::ASL, 1, 2, AddressMode::Accumulator),
        OpCode::new(0x06, Mnemonic::ASL, 2, 5, AddressMode::ZeroPage),
        OpCode::new(0x16, Mnemonic::ASL, 2, 6, AddressMode::ZeroPageX),
        OpCode::new(0x0E, Mnemonic::ASL, 3, 6, AddressMode::Absolute),
        OpCode::new(0x1E, Mnemonic::ASL, 3, 7, AddressMode::AbsoluteX),
        //// LSR
        OpCode::new(0x4A, Mnemonic::LSR, 1, 2, AddressMode::Accumulator),
        OpCode::new(0x46, Mnemonic::LSR, 2, 5, AddressMode::ZeroPage),
        OpCode::new(0x56, Mnemonic::LSR, 2, 6, AddressMode::ZeroPageX),
        OpCode::new(0x4E, Mnemonic::LSR, 3, 6, AddressMode::Absolute),
        OpCode::new(0x5E, Mnemonic::LSR, 3, 7, AddressMode::AbsoluteX),
        //// ROL
        OpCode::new(0x2A, Mnemonic::ROL, 1, 2, AddressMode::Accumulator),
        OpCode::new(0x26, Mnemonic::ROL, 2, 5, AddressMode::ZeroPage),
        OpCode::new(0x36, Mnemonic::ROL, 2, 6, AddressMode::ZeroPageX),
        OpCode::new(0x2E, Mnemonic::ROL, 3, 6, AddressMode::Absolute),
        //// ROR
        OpCode::new(0x6A, Mnemonic::ROR, 1, 2, AddressMode::Accumulator),
        OpCode::new(0x66, Mnemonic::ROR, 2, 5, AddressMode::ZeroPage),
        OpCode::new(0x76, Mnemonic::ROR, 2, 6, AddressMode::ZeroPageX),
        OpCode::new(0x6E, Mnemonic::ROR, 3, 6, AddressMode::Absolute),

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

        // JMP
        OpCode::new(0x4c, Mnemonic::JMP, 3, 3, AddressMode::Absolute),
        OpCode::new(0x6c, Mnemonic::JMP, 3, 5, AddressMode::Indirect),
        OpCode::new(0x20, Mnemonic::JSR, 3, 6, AddressMode::Absolute),
        OpCode::new(0x60, Mnemonic::RTS, 1, 6, AddressMode::None),
        OpCode::new(0x40, Mnemonic::RTI, 1, 6, AddressMode::None),

        // Flags
        OpCode::new(0x38, Mnemonic::SEC, 1, 2, AddressMode::None),
        OpCode::new(0xf8, Mnemonic::SED, 1, 2, AddressMode::None),
        OpCode::new(0x78, Mnemonic::SEI, 1, 2, AddressMode::None),
        OpCode::new(0x18, Mnemonic::CLC, 1, 2, AddressMode::None),
        OpCode::new(0xd8, Mnemonic::CLD, 1, 2, AddressMode::None),
        OpCode::new(0x58, Mnemonic::CLI, 1, 2, AddressMode::None),
        OpCode::new(0xb8, Mnemonic::CLV, 1, 2, AddressMode::None),


        // Branches
        OpCode::new(0x10, Mnemonic::BPL, 2, 2, AddressMode::Relative),
        OpCode::new(0x30, Mnemonic::BMI, 2, 2, AddressMode::Relative),
        OpCode::new(0x50, Mnemonic::BVC, 2, 2, AddressMode::Relative),
        OpCode::new(0x70, Mnemonic::BVS, 2, 2, AddressMode::Relative),
        OpCode::new(0x90, Mnemonic::BCC, 2, 2, AddressMode::Relative),
        OpCode::new(0xb0, Mnemonic::BCS, 2, 2, AddressMode::Relative),
        OpCode::new(0xd0, Mnemonic::BNE, 2, 2, AddressMode::Relative),
        OpCode::new(0xf0, Mnemonic::BEQ, 2, 2, AddressMode::Relative),

        // Arithmetic
        //// ADC
        OpCode::new(0x69, Mnemonic::ADC, 2, 2, AddressMode::Immediate),
        OpCode::new(0x65, Mnemonic::ADC, 2, 3, AddressMode::ZeroPage),
        OpCode::new(0x75, Mnemonic::ADC, 2, 4, AddressMode::ZeroPageX),
        OpCode::new(0x6d, Mnemonic::ADC, 3, 4, AddressMode::Absolute),
        OpCode::new(0x7d, Mnemonic::ADC, 3, 4, AddressMode::AbsoluteX),
        OpCode::new(0x79, Mnemonic::ADC, 3, 4, AddressMode::AbsoluteY),
        OpCode::new(0x61, Mnemonic::ADC, 2, 6, AddressMode::IndirectX),
        OpCode::new(0x71, Mnemonic::ADC, 2, 5, AddressMode::IndirectY),
        //// SBC
        OpCode::new(0xe9, Mnemonic::SBC, 2, 2, AddressMode::Immediate),
        OpCode::new(0xe5, Mnemonic::SBC, 2, 3, AddressMode::ZeroPage),
        OpCode::new(0xf5, Mnemonic::SBC, 2, 4, AddressMode::ZeroPageX),
        OpCode::new(0xed, Mnemonic::SBC, 3, 4, AddressMode::Absolute),
        OpCode::new(0xfd, Mnemonic::SBC, 3, 4, AddressMode::AbsoluteX),
        OpCode::new(0xf9, Mnemonic::SBC, 3, 4, AddressMode::AbsoluteY),
        OpCode::new(0xe1, Mnemonic::SBC, 2, 6, AddressMode::IndirectX),
        OpCode::new(0xf1, Mnemonic::SBC, 2, 5, AddressMode::IndirectY),
        //// CMP
        OpCode::new(0xc9, Mnemonic::CMP, 2, 2, AddressMode::Immediate),
        OpCode::new(0xc5, Mnemonic::CMP, 2, 3, AddressMode::ZeroPage),
        OpCode::new(0xd5, Mnemonic::CMP, 2, 4, AddressMode::ZeroPageX),
        OpCode::new(0xcd, Mnemonic::CMP, 3, 4, AddressMode::Absolute),
        OpCode::new(0xdd, Mnemonic::CMP, 3, 4, AddressMode::AbsoluteX),
        OpCode::new(0xd9, Mnemonic::CMP, 3, 4, AddressMode::AbsoluteY),
        OpCode::new(0xc1, Mnemonic::CMP, 2, 6, AddressMode::IndirectX),
        OpCode::new(0xd1, Mnemonic::CMP, 2, 5, AddressMode::IndirectY),
        //// CPX
        OpCode::new(0xe0, Mnemonic::CPX, 2, 2, AddressMode::Immediate),
        OpCode::new(0xe4, Mnemonic::CPX, 2, 3, AddressMode::ZeroPage),
        OpCode::new(0xec, Mnemonic::CPX, 3, 4, AddressMode::Absolute),
        //// CPY
        OpCode::new(0xc0, Mnemonic::CPY, 2, 2, AddressMode::Immediate),
        OpCode::new(0xc4, Mnemonic::CPY, 2, 3, AddressMode::ZeroPage),
        OpCode::new(0xcc, Mnemonic::CPY, 3, 4, AddressMode::Absolute),

    ];

    pub static ref OPCODE_MAP: HashMap<u8, &'static OpCode> = OPCODES.iter().fold(HashMap::new(), |mut map, opcode| {
        map.insert(opcode.code, opcode);
        map
    });
}
