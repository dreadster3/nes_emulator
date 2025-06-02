pub mod cpu;
pub mod opcodes;

fn main() {
    let mut cpu = cpu::CPU::new();
    let program: Vec<u8> = vec![0xa9, 0x05, 0x00];

    match cpu.load_and_run(program) {
        Ok(()) => println!("{:?}", cpu),
        Err(err) => eprintln!("Error: {}", err),
    }
}
