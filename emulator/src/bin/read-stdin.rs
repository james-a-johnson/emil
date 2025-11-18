use std::any::Any;
use std::collections::VecDeque;

use binaryninja::binary_view::{BinaryViewBase, BinaryViewExt};
use binaryninja::headless::Session;

use emil::arch::{Little, RegState as _, State, arm64::*};
use emil::emil::ILVal;
use emil::emulate::{Emulate, Emulator, Exit, HookStatus};
use emil::load::*;
use emil::os::linux::{AuxVal, Environment, add_default_auxv};
use emil::prog::Program;

use softmew::Perm;
use softmew::page::{Page, SimplePage};

const STACK_BASE: usize = 0xfffffffffff00000;
const STACK_SIZE: usize = 0x000000000007f000;

fn main() {
    let functions_to_load: &[u64] = &[
        0x423a10, 0x40fa10, 0x400850, 0x425160, 0x44b910, 0x424780, 0x4253d0, 0x415b00, 0x400300,
        0x406984, 0x406090, 0x418400, 0x406984, 0x453860,
    ];
    let headless_session = Session::new().expect("Failed to create new session");
    let bv = headless_session
        .load("./test-bins/sum-stdin-arm.bndb")
        .expect("Couldn't load test binary");

    let mut prog = Program::<SimplePage, Arm64State, Little, ArmIntrinsic>::default();
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
    // fatal error
    prog.add_empty(0x4240e0);
    // rindex
    prog.add_empty(0x447c80);
    // strchrnul
    prog.add_empty(0x41cc80);
    for addr in functions_to_load {
        load_function(&mut prog, &bv, *addr)
            .map_err(|e| format!("Loading {:#x} failed: {}", *addr, e))
            .unwrap();
    }

    let mut stdin = VecDeque::new();
    stdin.extend(b"10\n11\n12\n13\n");
    let mut state = LinuxArm64::new(c"/home/user/read-stdin", 0x80000000..0x80100000);
    state.set_stdin(stdin);
    let mem = state.memory_mut();
    load_sections(mem, &bv).expect("Failed to load a section");
    let stack = mem
        .map_memory(STACK_BASE, STACK_SIZE, Perm::READ | Perm::WRITE)
        .unwrap();

    let mut env = Environment::default();
    env.args.push("read-stdin".into());
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
    emu.add_hook(0x400300, strlen_hook).unwrap();
    emu.add_hook(0x41e1c0, memset_hook).unwrap();
    emu.add_hook(0x447c80, rindex_hook).unwrap();
    emu.add_hook(0x41cc80, strchrnul).unwrap();

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
    println!("{message}");
}

fn strlen_hook<P: Page>(
    state: &mut dyn State<P, Registers = Arm64State, Endianness = Little, Intrin = ArmIntrinsic>,
) -> HookStatus {
    let mut addr = state.regs().read(Arm64Reg::x0).extend_64() as usize;
    let ret = state.regs().read(Arm64Reg::lr).extend_64();
    let mut buf = [0u8];
    let mut len = 0u64;
    loop {
        let _ = state.mem().read_perm(addr, &mut buf);
        if buf[0] == 0 {
            break;
        }
        addr += 1;
        len += 1;
    }
    state
        .regs()
        .write(Arm64Reg::x0, emil::emil::ILVal::Quad(len));
    HookStatus::Goto(ret)
}

fn memset_hook<P: Page>(
    state: &mut dyn State<P, Registers = Arm64State, Endianness = Little, Intrin = ArmIntrinsic>,
) -> HookStatus {
    let src = state.regs().read(Arm64Reg::x0).get_quad() as usize;
    let val = state.regs().read(Arm64Reg::w1).truncate(1).get_byte();
    let size = state.regs().read(Arm64Reg::x2).get_quad() as usize;
    let ret = state.regs().read(Arm64Reg::lr).get_quad();

    match state.mem().get_slice_mut(src..src + size, Perm::WRITE) {
        Ok(mem) => mem.fill(val),
        Err(e) => return HookStatus::Fault(e),
    };
    HookStatus::Goto(ret)
}

fn rindex_hook<P: Page>(
    state: &mut dyn State<P, Registers = Arm64State, Endianness = Little, Intrin = ArmIntrinsic>,
) -> HookStatus {
    let mut src = state.regs().read(Arm64Reg::x0).get_quad() as usize;
    let val = state.regs().read(Arm64Reg::x1).truncate(1).get_byte();
    let ret = state.regs().read(Arm64Reg::lr).get_quad();

    let mut buf = [0u8];
    let mut last: Option<u64> = None;
    loop {
        let _ = state.mem().read_perm(src, &mut buf);
        if buf[0] == val {
            last = Some(src as u64);
        }
        if buf[0] == 0 {
            break;
        }
        src += 1;
    }

    match last {
        Some(addr) => state
            .regs()
            .write(Arm64Reg::x0, emil::emil::ILVal::Quad(addr)),
        None => state.regs().write(Arm64Reg::x0, emil::emil::ILVal::Quad(0)),
    };

    HookStatus::Goto(ret)
}

fn strchrnul<P: Page>(
    state: &mut dyn State<P, Registers = Arm64State, Endianness = Little, Intrin = ArmIntrinsic>,
) -> HookStatus {
    let ret = state.regs().read(Arm64Reg::lr).get_quad();
    let mut str_ptr = state.regs().read(Arm64Reg::x0).get_quad() as usize;
    let chr = state.regs().read(Arm64Reg::x1).truncate(1).get_byte();
    let mut byte = [0u8];

    loop {
        match state.mem().read_perm(str_ptr, &mut byte) {
            Ok(_) => {}
            Err(e) => return HookStatus::Fault(e),
        };
        if byte[0] == 0 || byte[0] == chr {
            state
                .regs()
                .write(Arm64Reg::x0, ILVal::Quad(str_ptr as u64));
            break;
        }
        str_ptr += 1;
    }

    HookStatus::Goto(ret)
}
