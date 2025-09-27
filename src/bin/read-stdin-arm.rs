use std::any::Any;
use std::collections::VecDeque;
use std::io::Write;

use binaryninja::binary_view::{BinaryViewBase, BinaryViewExt};
use binaryninja::headless::Session;

use emil::arch::{State, arm64::*};
use emil::emulate::{Emulator, Exit, HookStatus, Little};
use emil::os::linux::{AuxVal, Environment};
use emil::prog::Program;

use softmew::Perm;

const STACK_BASE: usize = 0xfffffffffff00000;
const STACK_SIZE: usize = 0x000000000007f000;

fn main() {
    let functions_to_load: &[u64] = &[0x423a10, 0x40fa10];
    let headless_session = Session::new().expect("Failed to create new session");
    let bv = headless_session
        .load("./test-bins/sum-stdin-arm.bndb")
        .expect("Couldn't load test binary");

    let mut prog = Program::<Arm64Reg, Little, ArmIntrinsic>::default();
    let entry = bv
        .function_at(bv.default_platform().unwrap().as_ref(), bv.entry_point())
        .unwrap();
    let llil_entry = entry.low_level_il().unwrap();
    prog.add_function(llil_entry.as_ref());
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
    // emu.add_breakpoint(0x423aac).unwrap();
    // emu.add_breakpoint(0x423ab8).unwrap();
    // emu.add_breakpoint(0x423abc).unwrap();
    // emu.add_breakpoint(0x423a70);
    let mut stop_reason: Exit;
    emu.set_pc(bv.entry_point());
    loop {
        stop_reason = emu.proceed();
        if let Exit::InstructionFault(addr) = stop_reason {
            let func = bv.function_at(bv.default_platform().unwrap().as_ref(), addr);
            match func {
                Some(f) => {
                    println!("Adding: {:?}", f.symbol().full_name());
                    emu.get_prog_mut()
                        .add_function(f.low_level_il().unwrap().as_ref());
                }
                None => {
                    println!("Fault hit address that isn't start of a function");
                    break;
                }
            }
        } else if let Exit::UserBreakpoint = stop_reason
            && emu.curr_pc() == 0x423aac
        {
            let x20 = emu.get_state().regs[Arm64Reg::x20];
            let x1 = emu.get_state().regs[Arm64Reg::x1];
            let sum = x20 + x1;
            println!("sum: {sum:#x}");
        } else if let Exit::UserBreakpoint = stop_reason
            && emu.curr_pc() == 0x423ab8
        {
            let x2 = emu.get_state().regs[Arm64Reg::x2];
            println!("x2: {x2:#x}");
        } else if let Exit::UserBreakpoint = stop_reason
            && emu.curr_pc() == 0x423a70
        {
            let x20 = emu.get_state().regs[Arm64Reg::x20];
            let x1 = emu.get_state().regs[Arm64Reg::x1];
            println!("arg0: {x20:#x}");
            println!("arg1: {x1:#x}");
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
