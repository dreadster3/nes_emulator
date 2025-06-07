extern crate sdl2;

pub mod bus;
pub mod cpu;
pub mod rom;

use bus::Bus;
use cpu::CPU;
use cpu::memory::Memory;
use rand::Rng;
use rom::ROM;
use sdl2::{EventPump, event::Event, keyboard::Keycode, pixels::Color, pixels::PixelFormatEnum};

fn color(byte: u8) -> Color {
    match byte {
        0 => sdl2::pixels::Color::BLACK,
        1 => sdl2::pixels::Color::WHITE,
        2 | 9 => sdl2::pixels::Color::GREY,
        3 | 10 => sdl2::pixels::Color::RED,
        4 | 11 => sdl2::pixels::Color::GREEN,
        5 | 12 => sdl2::pixels::Color::BLUE,
        6 | 13 => sdl2::pixels::Color::MAGENTA,
        7 | 14 => sdl2::pixels::Color::YELLOW,
        _ => sdl2::pixels::Color::CYAN,
    }
}

fn handle_user_input(cpu: &mut CPU, event_pump: &mut EventPump) {
    for event in event_pump.poll_iter() {
        match event {
            Event::Quit { .. }
            | Event::KeyDown {
                keycode: Some(Keycode::Escape),
                ..
            } => std::process::exit(0),
            Event::KeyDown {
                keycode: Some(Keycode::W),
                ..
            } => {
                cpu.mem_write_u8(0xff, 0x77);
            }
            Event::KeyDown {
                keycode: Some(Keycode::S),
                ..
            } => {
                cpu.mem_write_u8(0xff, 0x73);
            }
            Event::KeyDown {
                keycode: Some(Keycode::A),
                ..
            } => {
                cpu.mem_write_u8(0xff, 0x61);
            }
            Event::KeyDown {
                keycode: Some(Keycode::D),
                ..
            } => {
                cpu.mem_write_u8(0xff, 0x64);
            }
            _ => { /* do nothing */ }
        }
    }
}

fn read_screen_state(cpu: &CPU, frame: &mut [u8; 32 * 3 * 32]) -> bool {
    let mut frame_idx = 0;
    let mut update = false;
    for i in 0x0200..0x0600 {
        let color_idx = cpu.mem_read_u8(i as u16);
        let (b1, b2, b3) = color(color_idx).rgb();
        if frame[frame_idx] != b1 || frame[frame_idx + 1] != b2 || frame[frame_idx + 2] != b3 {
            frame[frame_idx] = b1;
            frame[frame_idx + 1] = b2;
            frame[frame_idx + 2] = b3;
            update = true;
        }
        frame_idx += 3;
    }
    update
}

fn main() {
    let sdl_context = sdl2::init().unwrap();
    let video_subsystem = sdl_context.video().unwrap();
    let window = video_subsystem
        .window("Snake game", (32.0 * 10.0) as u32, (32.0 * 10.0) as u32)
        .position_centered()
        .build()
        .unwrap();

    let mut canvas = window.into_canvas().present_vsync().build().unwrap();
    let mut event_pump = sdl_context.event_pump().unwrap();
    canvas.set_draw_color(sdl2::pixels::Color::RGB(0, 0, 0));
    canvas.set_scale(10f32, 10f32).unwrap();

    let creator = canvas.texture_creator();
    let mut texture = creator
        .create_texture_target(PixelFormatEnum::RGB24, 32, 32)
        .unwrap();

    let bytes = std::fs::read("snake.nes").unwrap();
    let rom = ROM::from_bytes(&bytes).unwrap();
    let bus = Bus::new(rom);
    let mut cpu = CPU::new(bus);
    cpu.reset();

    let mut screen_state = [0u8; 32 * 3 * 32];
    let mut rng = rand::rng();

    let result = cpu.run_with_callback(move |cpu| {
        handle_user_input(cpu, &mut event_pump);

        cpu.mem_write_u8(0xfe, rng.random_range(1..=16));

        if read_screen_state(cpu, &mut screen_state) {
            texture.update(None, &screen_state, 32 * 3).unwrap();

            canvas.copy(&texture, None, None).unwrap();

            canvas.present();
        }

        std::thread::sleep(std::time::Duration::new(0, 70_000));
    });

    match result {
        Ok(()) => println!("Program completed successfully"),
        Err(err) => {
            let program_counter = cpu.program_counter - 0x0600;
            let absolute_pc = cpu.program_counter;
            eprintln!(
                "Error: {err} at program counter {program_counter} (absolute: 0x{absolute_pc:04x})"
            );

            // Debug the problematic area
            eprintln!("Memory around PC:");
            for i in 0..10 {
                let addr = cpu.program_counter.saturating_sub(5).saturating_add(i);
                let val = cpu.mem_read_u8(addr);
                let marker = if addr == cpu.program_counter {
                    " <-- PC"
                } else {
                    ""
                };
                eprintln!("  0x{addr:04x}: 0x{val:02x}{marker}");
            }
        }
    }
}
