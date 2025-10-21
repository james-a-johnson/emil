use binaryninja::binary_view::{BinaryViewBase, BinaryViewExt};
use binaryninja::headless::Session;

use emil::arch::{SyscallResult, riscv::*};
use emil::emulate::{Emulator, Little};
use emil::os::linux::LinuxSyscalls;
use emil::prog::Program;
use softmew::page::SimplePage;
use softmew::{MMU, Perm};

#[derive(Default)]
pub struct RvMachine {
    stdout: Vec<u8>,
}

impl LinuxSyscalls<Rv64State, MMU<SimplePage>> for RvMachine {
    fn write(&mut self, regs: &mut Rv64State, mem: &mut MMU<SimplePage>) -> SyscallResult {
        let fd = regs[Rv64Reg::a0];
        let ptr = regs[Rv64Reg::a1];
        let len = regs[Rv64Reg::a2];
        let mut data = vec![0; len as usize];
        mem.read_perm(ptr as usize, &mut data)
            .expect("Failed to read message");
        match fd {
            1 => {
                self.stdout.extend_from_slice(&data);
                regs[Rv64Reg::a0] = len as u64;
            }
            _ => regs[Rv64Reg::a0] = len,
        }
        SyscallResult::Continue
    }
}

fn main() {
    let headless_session = Session::new().expect("Failed to create new session");
    let bv = headless_session
        .load("./test-bins/hello-riscv")
        .expect("Couldn't load test binary");

    let mut prog = Program::<Rv64Reg, Little, RVIntrinsic>::default();
    for func in &bv.functions() {
        prog.add_function(func.low_level_il().as_ref().unwrap());
    }

    for _ in 0..5 {
        println!("\n");
    }

    for _ in 0..5 {
        println!("\n");
    }

    let mut state = LinuxRV64::new(RvMachine::default());
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

    let stdout = String::from_utf8_lossy(&emu.get_state().syscalls.stdout);
    println!("{stdout}");
}
