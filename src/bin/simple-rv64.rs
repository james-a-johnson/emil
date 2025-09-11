use std::any::Any;

use binaryninja::binary_view::{BinaryViewBase, BinaryViewExt};
use binaryninja::headless::Session;

use emil::arch::riscv::*;
use emil::emulate::{Emulator, Little};
use emil::prog::Program;
use softmew::Perm;

#[derive(Clone, Default)]
struct Fd(Vec<u8>);

impl std::io::Read for Fd {
    fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> {
        Ok(0)
    }
}

impl std::io::Write for Fd {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fn main() {
    let headless_session = Session::new().expect("Failed to create new session");
    let bv = headless_session
        .load("/home/jaj/Documents/jamil/test-bins/hello-riscv")
        .expect("Couldn't load test binary");

    let mut prog = Program::<Rv64Reg, Little>::default();
    for func in &bv.functions() {
        prog.add_function(func.low_level_il().as_ref().unwrap());
    }

    let mut state = LinuxRV64::<0>::new();
    state.register_fd(1, Box::new(Fd::default()));
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

    let mut buffer = [0u8; 8];
    mem.read_perm(0x11168, &mut buffer).unwrap();

    let mut emu = Emulator::new(prog, state);
    let stop_reason = emu.run(bv.entry_point());
    println!("Stopped for: {:?}", stop_reason);

    let stdout = emu.get_state_mut().take_fd(1).unwrap() as Box<dyn Any>;
    let out: Box<Fd> = stdout.downcast().unwrap();
    let message = String::from_utf8(out.0).unwrap();
    println!("{message}");
}
