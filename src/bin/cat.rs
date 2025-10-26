use std::any::Any;
use std::collections::VecDeque;
use std::io::Write;

use binaryninja::binary_view::{BinaryViewBase, BinaryViewExt};
use binaryninja::headless::Session;

use emil::arch::arm64::*;
use emil::emulate::{Emulator, Exit, Little};
use emil::load::*;
use emil::os::linux::{AuxVal, Environment, add_default_auxv};
use emil::prog::Program;

use softmew::Perm;

const STACK_BASE: usize = 0xfffffffffff00000;
const STACK_SIZE: usize = 0x000000000007ffff;

use std::time::Instant;

const FUNCTION_ADDRS: &'static [u64] = &[
    0x403ef4, 0x403ecc, 0x405c44, 0x405a24, 0x400980, 0x40a90c, 0x40a864, 0x40a7e4, 0x40b20c,
    0x405a20, 0x405c0c, 0x405bd0, 0x400650, 0x400750, 0x4006b0, 0x40421c, 0x404174, 0x405c8c,
    0x4042e8, 0x401240, 0x401180, 0x401a00, 0x4042b4, 0x40406c, 0x4041d4, 0x404198, 0x401120,
    0x40404c, 0x404404, 0x404fa8, 0x404938, 0x401160, 0x400fb0, 0x4079f4, 0x407560, 0x404784,
    0x4056b4, 0x4058e8, 0x4058b0, 0x405d08, 0x40a734, 0x40a710, 0x400790, 0x4048fc, 0x4047f8,
    0x405388, 0x40a78c, 0x40434c, 0x4043ac, 0x40a7b8, 0x40a738, 0x407f08, 0x40430c, 0x400660,
    0x405ccc, 0x405cd0, 0x4006f0, 0x400680, 0x40b454, 0x40b39c, 0x40857c, 0x40a5b8, 0x40b32c,
    0x40aabc, 0x403eb0,
];

fn main() {
    let init = Instant::now();
    let headless_session = Session::new().expect("Failed to create new session");
    let bv = headless_session
        .load("../busybox-musl.bndb")
        .expect("Couldn't load test binary");

    let mut prog = Program::<Arm64Reg, Little, ArmIntrinsic>::default();
    let entry = bv
        .function_at(bv.default_platform().unwrap().as_ref(), bv.entry_point())
        .unwrap();
    // let llil_entry = entry.low_level_il().unwrap();
    // prog.add_function(llil_entry.as_ref());

    let load = Instant::now();
    for func_addr in FUNCTION_ADDRS {
        let func = bv
            .function_at(bv.default_platform().unwrap().as_ref(), *func_addr)
            .unwrap();
        let llil = func.low_level_il().unwrap();
        prog.add_function(llil.as_ref());
    }

    let mut state = LinuxArm64::new(ArmMachine::new(c"/usr/bin/echo", 0x80000000..0x80100000));
    let mem = state.memory_mut();
    load_sections(mem, &bv).expect("Failed to load a section");
    let stack = mem
        .map_memory(STACK_BASE, STACK_SIZE, Perm::READ | Perm::WRITE)
        .unwrap();

    let mut env = Environment::default();
    env.args
        .push("../../repos/busybox/busybox_unstripped".into());
    env.args.push("cat".into());
    env.args.push("./src/bin/cat.rs".into());
    env.env.push("EMULATOR=1".into());
    env.env.push("LANG=en_US.UTF-8".into());
    env.aux.push(AuxVal::Phnum(6));
    env.aux.push(AuxVal::Phdr(0x400040));
    env.aux.push(AuxVal::Phent(0x38));
    env.aux.push(AuxVal::Hwcap(0b10000000));
    add_default_auxv(&mut env.aux, &bv);
    let sp_val = env
        .encode(stack.as_mut(), (STACK_BASE + STACK_SIZE) as u64)
        .unwrap();

    let mut stack_file = std::fs::File::create("./stack.bin").unwrap();
    stack_file.write_all(stack.as_ref()).unwrap();

    let _heap = mem
        .map_memory(0x80000000, 0x100000, Perm::READ | Perm::WRITE)
        .unwrap();

    state.regs_mut()[Arm64Reg::sp] = sp_val;

    let mut emu = Emulator::new(prog, state);

    let mut stop_reason: Exit;
    emu.set_pc(entry.start());
    loop {
        let emulation = Instant::now();
        stop_reason = emu.proceed();
        let end = Instant::now();
        println!("Emulation: {:?}", end - emulation);
        println!("Load: {:?}", end - load);
        println!("All: {:?}", end - init);
        if let Exit::InstructionFault(addr) = stop_reason {
            let func = bv.function_at(bv.default_platform().unwrap().as_ref(), addr);
            match func {
                Some(f) => {
                    emu.get_prog_mut()
                        .add_function(f.low_level_il().unwrap().as_ref());
                }
                None => {
                    println!("Fault hit address that isn't start of a function");
                    break;
                }
            }
        } else {
            break;
        }
    }
    println!("Stop reason: {:?}", stop_reason);
    println!("Stopped at: {:#x}", emu.curr_pc());
    println!("Num EMIL instructions: {}", unsafe {
        emil::emulate::NUM_INSTRUCTIONS
    });

    let stdout: Box<dyn Any> = emu.get_state_mut().syscalls.take_fd(1).unwrap();
    let mut stdout: Box<VecDeque<u8>> = stdout.downcast().unwrap();
    let message = String::from_utf8(stdout.make_contiguous().to_vec()).unwrap();
    println!("stdout: {message}");

    let stderr: Box<dyn Any> = emu.get_state_mut().syscalls.take_fd(2).unwrap();
    let mut stderr: Box<VecDeque<u8>> = stderr.downcast().unwrap();
    let message = String::from_utf8(stderr.make_contiguous().to_vec()).unwrap();
    println!("stderr: {message}");
}
