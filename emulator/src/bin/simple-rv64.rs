use std::any::Any;
use std::collections::VecDeque;

use binaryninja::binary_view::{BinaryViewBase, BinaryViewExt};
use binaryninja::headless::Session;

use emil::arch::{Little, riscv::*};
use emil::emulate::{Emulate, Emulator};
use emil::prog::Program;
use softmew::Perm;
use softmew::page::SimplePage;

fn main() {
    let headless_session = Session::new().expect("Failed to create new session");
    let bv = headless_session
        .load("./test-bins/hello-riscv")
        .expect("Couldn't load test binary");

    let mut prog = Program::<SimplePage, Rv64State, Little, RVIntrinsic>::default();
    for func in &bv.functions() {
        prog.add_function(func.low_level_il().as_ref().unwrap());
    }

    for _ in 0..5 {
        println!("\n");
    }

    for _ in 0..5 {
        println!("\n");
    }

    let mut state = LinuxRV64::new(0..0x1000);
    let mem = state.memory_mut();
    for segment in bv.segments().iter() {
        let mut perm = Perm::NONE;
        let range = segment.address_range();
        println!("Mapping: {:?}", range);
        if segment.readable() {
            perm |= Perm::READ;
        }
        if segment.writable() {
            perm |= Perm::WRITE;
        }
        let mem_seg = mem
            .map_memory(
                range.start as usize,
                (range.end - range.start) as usize,
                perm,
            )
            .expect("Failed to map segment");
        bv.read(mem_seg.as_mut(), range.start);
    }

    let mut emu = Emulator::new(prog, state);
    let stop_reason = emu.run(bv.entry_point());
    println!("Stopped for: {:?}", stop_reason);

    let stdout: Box<dyn Any> = emu.get_state_mut().take_fd(1).unwrap();
    let mut stdout: Box<VecDeque<u8>> = stdout.downcast().unwrap();
    let message = String::from_utf8(stdout.make_contiguous().to_vec()).unwrap();
    println!("stdout: {message}");
}
