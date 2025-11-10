use std::any::Any;
use std::collections::VecDeque;

use binaryninja::binary_view::{BinaryViewBase, BinaryViewExt};
use binaryninja::headless::Session;

use emil::arch::{Little, arm64::*};
use emil::emulate::{Emulator, Exit};
use emil::load::*;
use emil::os::linux::{AuxVal, Environment, add_default_auxv};
use emil::prog::Program;

use softmew::Perm;
use softmew::page::SimplePage;

const STACK_BASE: usize = 0xfffffffffff00000;
const STACK_SIZE: usize = 0x000000000007ffff;

fn main() {
    let headless_session = Session::new().expect("Failed to create new session");
    let bv = headless_session
        .load("../busybox-musl.bndb")
        .expect("Couldn't load test binary");

    let mut prog = Program::<SimplePage, Arm64State, Little, ArmIntrinsic>::default();
    let entry = bv
        .function_at(bv.default_platform().unwrap().as_ref(), bv.entry_point())
        .unwrap();
    let llil_entry = entry.low_level_il().unwrap();
    prog.add_function(llil_entry.as_ref());

    let mut state = LinuxArm64::new(c"/usr/bin/echo", 0x80000000..0x80100000);
    let mem = state.memory_mut();
    load_sections(mem, &bv).expect("Failed to load a section");
    let stack = mem
        .map_memory(STACK_BASE, STACK_SIZE, Perm::READ | Perm::WRITE)
        .unwrap();

    let mut env = Environment::default();
    env.args
        .push("../../repos/busybox/busybox_unstripped".into());
    env.args.push("cat".into());
    env.args.push("./emulator/src/bin/cat.rs".into());
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

    let _heap = mem
        .map_memory(0x80000000, 0x100000, Perm::READ | Perm::WRITE)
        .unwrap();

    state.regs_mut()[Arm64Reg::sp] = sp_val;

    let mut emu = Emulator::new(prog, state);

    let mut stop_reason: Exit;
    emu.set_pc(entry.start());
    loop {
        stop_reason = emu.proceed();
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

    let stdout: Box<dyn Any> = emu.get_state_mut().take_fd(1).unwrap();
    let mut stdout: Box<VecDeque<u8>> = stdout.downcast().unwrap();
    let message = String::from_utf8(stdout.make_contiguous().to_vec()).unwrap();
    println!("stdout: {message}");

    let stderr: Box<dyn Any> = emu.get_state_mut().take_fd(2).unwrap();
    let mut stderr: Box<VecDeque<u8>> = stderr.downcast().unwrap();
    let message = String::from_utf8(stderr.make_contiguous().to_vec()).unwrap();
    println!("stderr: {message}");
}
