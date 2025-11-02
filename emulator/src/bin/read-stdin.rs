use std::any::Any;
use std::collections::VecDeque;

// use std::fs;
// use std::io::Write;

use binaryninja::binary_view::{BinaryViewBase, BinaryViewExt};
use binaryninja::headless::Session;

use emil::arch::{Endian, Little, State, riscv::*};
use emil::emil::ILVal;
use emil::emulate::{Emulator, Exit, HookStatus};
use emil::os::linux::{AuxVal, Environment};
use emil::prog::Program;

use softmew::Perm;

const STACK_BASE: usize = 0xfffffffffff00000;
const STACK_SIZE: usize = 0x000000000007f000;

fn main() {
    let required_functions: &[u64] = &[
        0x1054c, 0x1056e, 0x1073a, 0x29294, 0x29ce8, 0x47830, 0x47824, 0x28ae6, 0x10a90, 0x28962,
        0x281d2, 0x28fcc, 0x47848, 0x4783c, 0x26c18, 0x26bec, 0x24dfe, 0x24e92, 0x28988, 0x14b5c,
        0x14aa2, 0x223ba, 0x202fe, 0x208ac, 0x1f06e,
    ];
    let headless_session = Session::new().expect("Failed to create new session");
    let bv = headless_session
        .load("./test-bins/sum-stdin-imdc.bndb")
        .expect("Couldn't load test binary");

    let mut prog = Program::<Rv64Reg, Little, RVIntrinsic>::default();
    for func in required_functions {
        let bin_func = bv
            .function_at(bv.default_platform().unwrap().as_ref(), *func)
            .unwrap();
        if let Ok(llil_func) = bin_func.low_level_il().as_ref() {
            prog.add_function(llil_func);
        }
    }

    let mut stdin = VecDeque::new();
    stdin.extend(b"10\n11\n12\n13\n");
    let mut state = LinuxRV64::new(RvMachine::new(0x80000000..0x80010000));
    state.syscalls.set_stdin(stdin);
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
    let stack = mem
        .map_memory(STACK_BASE, STACK_SIZE, Perm::READ | Perm::WRITE)
        .unwrap();

    let mut env = Environment::default();
    env.args.push("read-stdin".into());
    env.env.push("EMULATOR=1".into());
    env.aux.push(AuxVal::Uid(1000));
    env.aux.push(AuxVal::Euid(1000));
    env.aux.push(AuxVal::Gid(1000));
    env.aux.push(AuxVal::Egid(1000));
    env.aux.push(AuxVal::Random([
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
    ]));
    let sp_val = env
        .encode(stack.as_mut(), (STACK_BASE + STACK_SIZE) as u64)
        .unwrap();

    let _heap = mem
        .map_memory(0x80000000, 0x10000, Perm::READ | Perm::WRITE)
        .unwrap();

    state.regs_mut()[Rv64Reg::sp] = sp_val;

    let mut emu = Emulator::new(prog, state);
    emu.add_hook(0x14ac6, store_conditional_hook)
        .expect("Failed to install first hook");
    emu.add_hook(0x223dc, store_conditional_hook2)
        .expect("Failed to install second hook");
    emu.add_hook(0x20558, store_conditional_hook3)
        .expect("Failed to install third hook");
    emu.add_hook(0x223dc, store_conditional_hook4)
        .expect("Failed to install fourth hook");
    emu.add_hook(0x1f0a0, store_conditional_hook5)
        .expect("Failed to install fifth hook");
    emu.add_hook(0x20926, atomic_max_hook)
        .expect("Failed to install further hook");
    emu.add_hook(0x20938, atomic_max_hook2)
        .expect("Failed to install further hook");
    emu.add_hook(0x29318, compare_hook);
    let mut stop_reason: Exit;
    emu.set_pc(bv.entry_point());
    loop {
        stop_reason = emu.proceed();
        if let Exit::InstructionFault(addr) = stop_reason {
            let func = bv.function_at(bv.default_platform().unwrap().as_ref(), addr);
            match func {
                Some(f) => {
                    emu.get_prog_mut()
                        .add_function(f.low_level_il().unwrap().as_ref());
                    println!("Added: {:?}", f.symbol().full_name());
                }
                None => {
                    println!("Fault hit address that isn't start of a function");
                    break;
                }
            }
        } else if let Exit::UserBreakpoint = stop_reason {
            let s0 = emu.get_state().regs[Rv64Reg::s0];
            println!("s0: {:#x}", s0);
        } else {
            break;
        }
    }
    println!("Stop reason: {:?}", stop_reason);
    println!("Stopped at: {:#x}", emu.curr_pc());

    let stdout: Box<dyn Any> = emu.get_state_mut().syscalls.take_fd(1).unwrap();
    let mut stdout: Box<VecDeque<u8>> = stdout.downcast().unwrap();
    let message = String::from_utf8(stdout.make_contiguous().to_vec()).unwrap();
    println!("{message}");
}

fn compare_hook(
    state: &mut dyn State<Reg = Rv64Reg, Endianness = Little, Intrin = RVIntrinsic>,
) -> HookStatus {
    let t3 = state.read_reg(Rv64Reg::t3).extend_64();
    println!("t3 is: {:#?}", state.read_reg(Rv64Reg::t3));
    if t3 == 0 {
        HookStatus::Exit
    } else {
        HookStatus::Continue
    }
}

fn store_conditional_hook(
    state: &mut dyn State<Reg = Rv64Reg, Endianness = Little, Intrin = RVIntrinsic>,
) -> HookStatus {
    let mut buf = [0u8; 8];
    let addr = state.read_reg(Rv64Reg::a1).extend_64();
    let value = state.read_reg(Rv64Reg::a4).truncate(4);
    Little::write(value, &mut buf);
    let _ = state.write_mem(addr, &buf[0..4]);
    state.write_reg(Rv64Reg::a2, ILVal::Word(0));
    HookStatus::Goto(0x14aca)
}

fn store_conditional_hook2(
    state: &mut dyn State<Reg = Rv64Reg, Endianness = Little, Intrin = RVIntrinsic>,
) -> HookStatus {
    let mut buf = [0u8; 8];
    let addr = state.read_reg(Rv64Reg::s0).extend_64();
    let value = state.read_reg(Rv64Reg::a4).truncate(4);
    Little::write(value, &mut buf);
    let _ = state.write_mem(addr, &buf[0..4]);
    state.write_reg(Rv64Reg::a3, ILVal::Word(0));
    HookStatus::Goto(0x223e0)
}

fn store_conditional_hook3(
    state: &mut dyn State<Reg = Rv64Reg, Endianness = Little, Intrin = RVIntrinsic>,
) -> HookStatus {
    let mut buf = [0u8; 8];
    let addr = state.read_reg(Rv64Reg::a0).extend_64();
    let value = state.read_reg(Rv64Reg::a3);
    Little::write(value, &mut buf);
    let _ = state.write_mem(addr, &buf);
    state.write_reg(Rv64Reg::a2, ILVal::Word(0));
    HookStatus::Goto(0x2055c)
}

fn store_conditional_hook4(
    state: &mut dyn State<Reg = Rv64Reg, Endianness = Little, Intrin = RVIntrinsic>,
) -> HookStatus {
    let mut buf = [0u8; 8];
    let addr = state.read_reg(Rv64Reg::s0).extend_64();
    let value = state.read_reg(Rv64Reg::a4).truncate(4);
    Little::write(value, &mut buf);
    let _ = state.write_mem(addr, &buf[0..4]);
    state.write_reg(Rv64Reg::a3, ILVal::Word(0));
    HookStatus::Goto(0x223e0)
}

fn store_conditional_hook5(
    state: &mut dyn State<Reg = Rv64Reg, Endianness = Little, Intrin = RVIntrinsic>,
) -> HookStatus {
    let mut buf = [0u8; 8];
    let addr = state.read_reg(Rv64Reg::a5).extend_64();
    let value = state.read_reg(Rv64Reg::a4).truncate(4);
    Little::write(value, &mut buf);
    let _ = state.write_mem(addr, &buf[0..4]);
    state.write_reg(Rv64Reg::a2, ILVal::Word(0));
    HookStatus::Goto(0x1f0a4)
}

fn atomic_max_hook(
    state: &mut dyn State<Reg = Rv64Reg, Endianness = Little, Intrin = RVIntrinsic>,
) -> HookStatus {
    let mut buf = [0u8; 8];
    let addr = state.read_reg(Rv64Reg::a3).extend_64();
    let cmp = state.read_reg(Rv64Reg::a4).truncate(4);
    let _ = state.read_mem(addr, &mut buf[0..4]);
    let val = Little::read(&buf[0..4]);
    state.write_reg(Rv64Reg::a4, val.sext(8));
    let max = if cmp > val { cmp } else { val };
    Little::write(max, &mut buf);
    let _ = state.write_mem(addr, &buf[0..4]);
    HookStatus::Goto(0x2092a)
}

fn atomic_max_hook2(
    state: &mut dyn State<Reg = Rv64Reg, Endianness = Little, Intrin = RVIntrinsic>,
) -> HookStatus {
    let mut buf = [0u8; 8];
    let addr = state.read_reg(Rv64Reg::a5).extend_64();
    let cmp = state.read_reg(Rv64Reg::s0);
    let _ = state.read_mem(addr, &mut buf);
    let val = Little::read(&buf);
    state.write_reg(Rv64Reg::s0, val);
    let max = if cmp > val { cmp } else { val };
    Little::write(max, &mut buf);
    let _ = state.write_mem(addr, &buf);
    HookStatus::Goto(0x2093c)
}
