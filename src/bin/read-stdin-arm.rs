use std::any::Any;
use std::collections::VecDeque;
use std::io::Write;

use binaryninja::binary_view::{BinaryViewBase, BinaryViewExt};
use binaryninja::headless::Session;

use emil::arch::{State, arm64::*};
use emil::emil::ILVal;
use emil::emulate::{AccessType, Emulator, Exit, HookStatus, Little};
use emil::os::linux::{AuxVal, Environment};
use emil::prog::Program;

use softmew::Perm;

const STACK_BASE: usize = 0xfffffffffff00000;
const STACK_SIZE: usize = 0x000000000007f000;

fn main() {
    let functions_to_load: &[u64] = &[
        0x449440, 0x423a10, 0x40fa10, 0x400850, 0x425160, 0x44b910, 0x424780,
    ];
    let headless_session = Session::new().expect("Failed to create new session");
    let bv = headless_session
        .load("./test-bins/sum-stdin-arm.bndb")
        .expect("Couldn't load test binary");

    let mut prog = Program::<Arm64Reg, Little, ArmIntrinsic>::default();
    let entry = bv
        .function_at(bv.default_platform().unwrap().as_ref(), bv.entry_point())
        .unwrap();
    let main = bv
        .function_at(bv.default_platform().unwrap().as_ref(), 0x4006d4)
        .expect("No main function");
    let llil_entry = entry.low_level_il().unwrap();
    prog.add_function(llil_entry.as_ref());
    prog.add_function(main.low_level_il().unwrap().as_ref());
    // __strlen_asimd
    prog.add_empty(0x41e940);
    // memset generic
    prog.add_empty(0x41e1c0);
    prog.add_empty(0x4240e0);
    // _dlfo_process_initial
    prog.add_empty(0x459520);
    for addr in functions_to_load {
        let func = bv
            .function_at(bv.default_platform().unwrap().as_ref(), *addr)
            .unwrap();
        let llil = func.low_level_il().unwrap();
        prog.add_function(llil.as_ref());
    }

    let mut stdin = VecDeque::new();
    stdin.extend(b"10\n11\n12\n13\n");
    let mut state = LinuxArm64::new(ArmMachine::new(0x80000000..0x80010000));
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
    env.aux.push(AuxVal::Platform("aarch64".into()));
    env.aux.push(AuxVal::Uid(1000));
    env.aux.push(AuxVal::Euid(1000));
    env.aux.push(AuxVal::Gid(1000));
    env.aux.push(AuxVal::Egid(1000));
    env.aux.push(AuxVal::Phnum(6));
    env.aux.push(AuxVal::Phdr(0x400040));
    env.aux.push(AuxVal::Phent(0x38));
    env.aux.push(AuxVal::Random([
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
    ]));
    let sp_val = env
        .encode(stack.as_mut(), (STACK_BASE + STACK_SIZE) as u64)
        .unwrap();
    let mut stack_file = std::fs::File::create("stack.bin").unwrap();
    stack_file.write(stack.as_ref()).unwrap();

    // println!("Stack pointer is {:X}", sp_val);
    // let mut stack_file = fs::File::create("stack.bin").unwrap();
    // stack_file.write_all(stack.as_ref()).unwrap();

    let _heap = mem
        .map_memory(0x80000000, 0x10000, Perm::READ | Perm::WRITE)
        .unwrap();

    state.regs_mut()[Arm64Reg::sp] = sp_val;

    let mut emu = Emulator::new(prog, state);
    emu.add_hook(0x40fa10, libc_fatal_hook).unwrap();
    emu.add_hook(0x41e940, strlen_hook).unwrap();
    emu.add_hook(0x4240e0, fatal_hook).unwrap();
    emu.add_hook(0x41e1c0, memset_hook).unwrap();
    emu.add_hook(0x459520, return_zero_hook).unwrap();
    emu.add_breakpoint(0x424e8c).unwrap();
    emu.add_watch_addrs(0x4a7f98..0x4a7fa0, dl_platform_watch);
    let mut stop_reason: Exit;
    emu.set_pc(entry.start());
    loop {
        stop_reason = emu.proceed();
        if let Exit::InstructionFault(addr) = stop_reason {
            let func = bv.function_at(bv.default_platform().unwrap().as_ref(), addr);
            match func {
                Some(f) => {
                    println!("Adding: {:?} @ {:#x}", f.symbol().full_name(), addr);
                    emu.get_prog_mut()
                        .add_function(f.low_level_il().unwrap().as_ref());
                }
                None => {
                    println!("Fault hit address that isn't start of a function");
                    break;
                }
            }
        } else if let Exit::UserBreakpoint = stop_reason {
            let x19 = emu.get_state().regs[Arm64Reg::x19];
            println!("x19: {:#x}", x19);
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

fn libc_fatal_hook(
    state: &mut dyn State<Reg = Arm64Reg, Endianness = Little, Intrin = ArmIntrinsic>,
) -> HookStatus {
    println!("__libc_fatal called");
    let mut msg_ptr = state.read_reg(Arm64Reg::x0).extend_64();
    let mut message = Vec::new();
    let mut buf = [0u8];
    loop {
        state.read_mem(msg_ptr, &mut buf).unwrap();
        if buf[0] == 0 {
            break;
        }
        message.push(buf[0]);
        msg_ptr += 1;
    }
    let message = String::from_utf8(message).unwrap();
    println!("Fatal message: {}", message);
    HookStatus::Exit
}

fn fatal_hook(
    state: &mut dyn State<Reg = Arm64Reg, Endianness = Little, Intrin = ArmIntrinsic>,
) -> HookStatus {
    println!("fatal_error called");
    let mut msg_ptr = state.read_reg(Arm64Reg::x3).extend_64();
    let mut message = Vec::new();
    let mut buf = [0u8];
    loop {
        state.read_mem(msg_ptr, &mut buf).unwrap();
        if buf[0] == 0 {
            break;
        }
        message.push(buf[0]);
        msg_ptr += 1;
    }
    let message = String::from_utf8(message).unwrap();
    println!("Fatal message: {}", message);
    HookStatus::Exit
}

fn strlen_hook(
    state: &mut dyn State<Reg = Arm64Reg, Endianness = Little, Intrin = ArmIntrinsic>,
) -> HookStatus {
    let mut addr = state.read_reg(Arm64Reg::x0).extend_64();
    let ret = state.read_reg(Arm64Reg::lr).extend_64();
    let mut buf = [0u8];
    let mut len = 0u64;
    loop {
        let _ = state.read_mem(addr, &mut buf);
        if buf[0] == 0 {
            break;
        }
        addr += 1;
        len += 1;
    }
    state.write_reg(Arm64Reg::x0, emil::emil::ILVal::Quad(len));
    HookStatus::Goto(ret)
}

fn memset_hook(
    state: &mut dyn State<Reg = Arm64Reg, Endianness = Little, Intrin = ArmIntrinsic>,
) -> HookStatus {
    let mut src = state.read_reg(Arm64Reg::x0).extend_64();
    let mut dst = state.read_reg(Arm64Reg::x1).extend_64();
    let size = state.read_reg(Arm64Reg::x2).extend_64() as usize;
    let ret = state.read_reg(Arm64Reg::lr).extend_64();
    let mut buf = [0u8];
    for _ in 0..size {
        if state.read_mem(src, &mut buf).is_err() {
            return HookStatus::Continue;
        }
        if state.write_mem(dst, &buf).is_err() {
            return HookStatus::Continue;
        }
        src += 1;
        dst += 1;
    }
    HookStatus::Goto(ret)
}

fn return_zero_hook(
    state: &mut dyn State<Reg = Arm64Reg, Endianness = Little, Intrin = ArmIntrinsic>,
) -> HookStatus {
    state.write_reg(Arm64Reg::x0, ILVal::Quad(0));
    let ret = state.read_reg(Arm64Reg::lr).extend_64();
    HookStatus::Goto(ret)
}

fn dl_platform_watch(
    _state: &mut dyn State<Reg = Arm64Reg, Endianness = Little, Intrin = ArmIntrinsic>,
    pc: u64,
    _addr: u64,
    access: AccessType,
    _data: &mut [u8],
) {
    if access == AccessType::Read {
        return;
    }

    println!("dl platform modified by {:#x}", pc);
}
