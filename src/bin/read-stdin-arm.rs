use std::any::Any;
use std::collections::VecDeque;

use binaryninja::binary_view::{BinaryViewBase, BinaryViewExt};
use binaryninja::headless::Session;

use emil::arch::{State, arm64::*};
use emil::emil::ILVal;
use emil::emulate::{AccessType, Emulator, Exit, HookStatus, Little};
use emil::load::*;
use emil::os::linux::{AuxVal, Environment, add_default_auxv};
use emil::prog::Program;

use softmew::Perm;

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
    let mut state = LinuxArm64::new(ArmMachine::new(0x80000000..0x80100000));
    state.syscalls.set_stdin(stdin);
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

    // println!("Stack pointer is {:X}", sp_val);
    // let mut stack_file = fs::File::create("stack.bin").unwrap();
    // stack_file.write_all(stack.as_ref()).unwrap();

    let _heap = mem
        .map_memory(0x80000000, 0x100000, Perm::READ | Perm::WRITE)
        .unwrap();

    state.regs_mut()[Arm64Reg::sp] = sp_val;

    let mut emu = Emulator::new(prog, state);
    emu.add_hook(0x40fa10, libc_fatal_hook).unwrap();
    emu.add_hook(0x400300, strlen_hook).unwrap();
    emu.add_hook(0x4240e0, fatal_hook).unwrap();
    emu.add_hook(0x41e1c0, memset_hook).unwrap();
    emu.add_hook(0x415b00, malloc_assert).unwrap();
    emu.add_hook(0x447c80, rindex_hook).unwrap();
    emu.add_hook(0x41cc80, strchrnul).unwrap();
    emu.add_hook(0x453938, int_malloc).unwrap();
    emu.add_hook(0x45393c, int_malloc).unwrap();
    // emu.add_hook(0x4061c4, sum_hook).unwrap();
    // emu.add_hook(0x4061d4, sum_hook).unwrap();
    // emu.add_hook(0x406090, strtoul_hook).unwrap();
    // emu.add_hook(0x418bd0, int_malloc).unwrap();
    // emu.add_hook(0x418400, int_malloc_args).unwrap();
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
    let src = state.read_reg(Arm64Reg::x0).get_quad();
    let val = state.read_reg(Arm64Reg::w1).truncate(1).get_byte();
    let size = state.read_reg(Arm64Reg::x2).get_quad();
    let ret = state.read_reg(Arm64Reg::lr).get_quad();

    match state.get_mem_mut(src..src + size) {
        Ok(mem) => mem.fill(val),
        Err(e) => return HookStatus::Fault(e),
    };
    HookStatus::Goto(ret)
}

fn rindex_hook(
    state: &mut dyn State<Reg = Arm64Reg, Endianness = Little, Intrin = ArmIntrinsic>,
) -> HookStatus {
    let mut src = state.read_reg(Arm64Reg::x0).get_quad();
    let val = state.read_reg(Arm64Reg::x1).truncate(1).get_byte();
    let ret = state.read_reg(Arm64Reg::lr).get_quad();

    let mut buf = [0u8];
    let mut last: Option<u64> = None;
    loop {
        let _ = state.read_mem(src, &mut buf);
        if buf[0] == val {
            last = Some(src);
        }
        if buf[0] == 0 {
            break;
        }
        src += 1;
    }

    match last {
        Some(addr) => state.write_reg(Arm64Reg::x0, emil::emil::ILVal::Quad(addr)),
        None => state.write_reg(Arm64Reg::x0, emil::emil::ILVal::Quad(0)),
    };

    HookStatus::Goto(ret)
}

fn malloc_assert(
    state: &mut dyn State<Reg = Arm64Reg, Endianness = Little, Intrin = ArmIntrinsic>,
) -> HookStatus {
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
    println!("malloc assert: {}", message);
    HookStatus::Exit
}

fn strchrnul(
    state: &mut dyn State<Reg = Arm64Reg, Endianness = Little, Intrin = ArmIntrinsic>,
) -> HookStatus {
    let ret = state.read_reg(Arm64Reg::lr).get_quad();
    let mut str_ptr = state.read_reg(Arm64Reg::x0).get_quad();
    let chr = state.read_reg(Arm64Reg::x1).truncate(1).get_byte();
    let mut byte = [0u8];

    loop {
        match state.read_mem(str_ptr, &mut byte) {
            Ok(_) => {}
            Err(e) => return HookStatus::Fault(e),
        };
        if byte[0] == 0 || byte[0] == chr {
            state.write_reg(Arm64Reg::x0, ILVal::Quad(str_ptr));
            break;
        }
        str_ptr += 1;
    }

    HookStatus::Goto(ret)
}

fn sum_hook(
    state: &mut dyn State<Reg = Arm64Reg, Endianness = Little, Intrin = ArmIntrinsic>,
) -> HookStatus {
    let chr = state.read_reg(Arm64Reg::x19).get_quad();
    let idx = state.read_reg(Arm64Reg::x5).get_quad();
    println!("[{idx:#x}] = {chr}");
    HookStatus::Continue
}

fn strtoul_hook(
    state: &mut dyn State<Reg = Arm64Reg, Endianness = Little, Intrin = ArmIntrinsic>,
) -> HookStatus {
    let start = state.read_reg(Arm64Reg::x0).get_quad();
    let base = state.read_reg(Arm64Reg::x2).get_quad();

    let num = state.get_mem(start..start + 3).unwrap();
    println!("strtoul({:?}, {base})", num);
    HookStatus::Continue
}

fn int_malloc(
    state: &mut dyn State<Reg = Arm64Reg, Endianness = Little, Intrin = ArmIntrinsic>,
) -> HookStatus {
    let x2 = state.read_reg(Arm64Reg::x2).get_quad() as i64;
    let x3 = state.read_reg(Arm64Reg::x3).get_quad() as i64;
    let x6 = state.read_reg(Arm64Reg::x6).get_quad() as i64;

    println!("{x2}, {x3}, {x6}");

    HookStatus::Continue
}
