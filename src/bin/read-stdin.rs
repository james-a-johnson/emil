use std::any::Any;
use std::collections::VecDeque;

// use std::fs;
// use std::io::Write;

use binaryninja::binary_view::{BinaryViewBase, BinaryViewExt};
use binaryninja::headless::Session;

use jamil::arch::{State, riscv::*};
use jamil::emulate::{Emulator, Little};
use jamil::prog::Program;
use softmew::Perm;

const STACK_BASE: usize = 0xfffffffffff00000;
const STACK_SIZE: usize = 0x000000000007f000;

fn main() {
    let required_functions: &[u64] = &[
        0x1054c, 0x1056e, 0x1073a, 0x29294, 0x29ce8, 0x47830, 0x47824, 0x28ae6, 0x10a90, 0x28962,
        0x281d2, 0x28fcc, 0x47848, 0x4783c, 0x26c18, 0x26bec, 0x24dfe, 0x24e92,
    ];
    let headless_session = Session::new().expect("Failed to create new session");
    let bv = headless_session
        .load("/home/jaj/Documents/jamil/test-bins/sum-stdin.bndb")
        .expect("Couldn't load test binary");

    let mut prog = Program::<Rv64Reg, Little>::default();
    for func in required_functions {
        let bin_func = bv
            .function_at(bv.default_platform().unwrap().as_ref(), *func)
            .unwrap();
        if let Ok(llil_func) = bin_func.low_level_il().as_ref() {
            prog.add_function(llil_func);
        }
    }
    // for func in &bv.functions() {
    //     println!("Function: {:?}", func.symbol().full_name());
    //     if let Ok(llil_func) = func.low_level_il().as_ref() {
    //         prog.add_function(llil_func);
    //     }
    // }

    let mut stdin = VecDeque::new();
    stdin.extend(b"10\n11\n12\n13\n");
    let stdout = VecDeque::new();
    let mut state = LinuxRV64::<0>::new();
    state.register_fd(0, Box::new(stdin));
    state.register_fd(1, Box::new(stdout));
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
    let sp_val = env
        .encode(stack.as_mut(), (STACK_BASE + STACK_SIZE) as u64)
        .unwrap();

    // println!("Stack pointer is {:X}", sp_val);
    // let mut stack_file = fs::File::create("stack.bin").unwrap();
    // stack_file.write_all(stack.as_ref()).unwrap();

    let _heap = mem
        .map_memory(0x80000000, 0x10000, Perm::READ | Perm::WRITE)
        .unwrap();

    state.regs_mut()[Rv64Reg::sp] = sp_val;
    state.set_heap(0x80000000, 0x10000);

    let mut emu = Emulator::new(prog, state);
    emu.add_hook(0x24ea6, compare_hook);
    let stop_reason = emu.run(bv.entry_point());
    println!("Stopped for: {:?}", stop_reason);
    println!("Stopped at 0x{:X}", emu.curr_pc());

    let stdout = emu.get_state_mut().take_fd(1).unwrap() as Box<dyn Any>;
    let mut out: Box<VecDeque<u8>> = stdout.downcast().unwrap();
    let message = String::from_utf8(out.make_contiguous().to_vec()).unwrap();
    println!("{message}");
}

fn compare_hook(state: &mut dyn State<Reg = Rv64Reg, Endianness = Little>) {
    println!("Arg 1: {:#?}", state.read_reg(Rv64Reg::a5));
}
