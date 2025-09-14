use std::collections::{HashMap, VecDeque};
use std::io::{Read, Write};

// use std::fs;
// use std::io::Write;

use binaryninja::binary_view::{BinaryViewBase, BinaryViewExt};
use binaryninja::headless::Session;

use emil::arch::{riscv::*, State, SyscallResult};
use emil::emil::ILVal;
use emil::emulate::{Emulator, Endian, Exit, HookStatus, Little};
use emil::prog::Program;
use emil::os::linux::{AuxVal, Environment, LinuxSyscalls};
use softmew::page::{Page, SimplePage};
use softmew::{Perm, MMU};
use std::ops::Range;

const STACK_BASE: usize = 0xfffffffffff00000;
const STACK_SIZE: usize = 0x000000000007f000;

pub struct RvMachine {
    fds: HashMap<u32, VecDeque<u8>>,
    heap: Range<u64>,
}

impl RvMachine {
    pub fn new(heap: Range<u64>) -> Self {
        let mut map = HashMap::new();
        map.insert(0, VecDeque::new());
        map.insert(1, VecDeque::new());
        map.insert(2, VecDeque::new());
        Self {
            fds: map,
            heap,
        }
    }

    pub fn take_fd(&mut self, fd: u32) -> Option<VecDeque<u8>> {
        self.fds.remove(&fd)
    }

    pub fn set_stdin(&mut self, data: VecDeque<u8>) -> Option<VecDeque<u8>> {
        self.fds.insert(0, data)
    }
}

impl LinuxSyscalls<Rv64State, MMU<SimplePage>> for RvMachine {
    fn faccessat(&mut self, regs: &mut Rv64State, _mem: &mut MMU<SimplePage>) -> SyscallResult {
        regs[Rv64Reg::a0] = (-2_i64) as u64;
        SyscallResult::Continue
    }

    fn read(&mut self, regs: &mut Rv64State, mem: &mut MMU<SimplePage>) -> SyscallResult {
        let fd = regs[Rv64Reg::a0];
        let ptr = regs[Rv64Reg::a1] as usize;
        let len = regs[Rv64Reg::a2] as usize;
        match self.fds.get_mut(&(fd as u32)) {
            Some(file) => {
                let page = mem.get_mapping_mut(ptr).unwrap();
                let start = page.start();
                let buf = &mut page.as_mut()[ptr - start..][..len];
                let res = file.read(buf);
                match res {
                    Ok(b) => regs[Rv64Reg::a0] = b as u64,
                    Err(e) => {
                        regs[Rv64Reg::a0] = e.raw_os_error().unwrap_or(-9) as u64;
                    }
                }
            }
            None => regs[Rv64Reg::a0] = (-9_i64) as u64,
        };
        SyscallResult::Continue
    }

    fn write(&mut self, regs: &mut Rv64State, mem: &mut MMU<SimplePage>) -> SyscallResult {
        let fd = regs[Rv64Reg::a0];
        let ptr = regs[Rv64Reg::a1];
        let len = regs[Rv64Reg::a2];
        let mut data = vec![0; len as usize];
        mem .read_perm(ptr as usize, &mut data)
            .expect("Failed to read message");
        match self.fds.get_mut(&(fd as u32)) {
            Some(file) => {
                let res = file.write(&data);
                match res {
                    Ok(b) => regs[Rv64Reg::a0] = b as u64,
                    Err(e) => {
                        regs[Rv64Reg::a0] = e.raw_os_error().unwrap_or(-9) as u64;
                    }
                }
            }
            None => regs[Rv64Reg::a0] = len,
        }
        SyscallResult::Continue
    }

    fn set_tid_address(&mut self, regs: &mut Rv64State, _mem: &mut MMU<SimplePage>) -> SyscallResult {
        regs[Rv64Reg::a0] = 100;
        SyscallResult::Continue
    }

    fn set_robust_list(&mut self, regs: &mut Rv64State, _mem: &mut MMU<SimplePage>) -> SyscallResult {
        regs[Rv64Reg::a0] = 0;
        SyscallResult::Continue
    }

    fn uname(&mut self, regs: &mut Rv64State, mem: &mut MMU<SimplePage>) -> SyscallResult {
        let addr = regs[Rv64Reg::a0];
        regs[Rv64Reg::a0] = (-14_i64) as u64;
        if mem.write_perm(addr as usize, b"Linux\x00").is_err() {
            return SyscallResult::Continue;
        }
        if mem.write_perm((addr + 65) as usize, b"binja.emu\x00").is_err() {
            return SyscallResult::Continue;
        }
        if mem.write_perm((addr + 65 * 2) as usize, b"6.0\x00").is_err() {
            return SyscallResult::Continue;
        }
        if mem.write_perm((addr + 65 * 3) as usize, b"6.0\x00").is_err() {
            return SyscallResult::Continue;
        }
        if mem.write_perm((addr + 65 * 4) as usize, b"rv64gc\x00").is_err() {
            return SyscallResult::Continue;
        }
        if mem.write_perm((addr + 65 * 5) as usize, b"binja.emu\x00").is_err() {
            return SyscallResult::Continue;
        }
        regs[Rv64Reg::a0] = 0;
        SyscallResult::Continue
    }

    fn getrandom(&mut self, regs: &mut Rv64State, mem: &mut MMU<SimplePage>) -> SyscallResult {
        let addr = regs[Rv64Reg::a0];
        let size = regs[Rv64Reg::a1];
        regs[Rv64Reg::a0] = (-14_i64) as u64;
        for i in addr..(addr + size) {
            if mem.write_perm(i as usize, &[0xee]).is_err() {
                return SyscallResult::Continue
            }
        }

        regs[Rv64Reg::a0] = 0;
        SyscallResult::Continue
    }

    fn getuid(&mut self, regs: &mut Rv64State, _mem: &mut MMU<SimplePage>) -> SyscallResult {
        regs[Rv64Reg::a0] = 1000;
        SyscallResult::Continue
    }

    fn geteuid(&mut self, regs: &mut Rv64State, _mem: &mut MMU<SimplePage>) -> SyscallResult {
        regs[Rv64Reg::a0] = 1000;
        SyscallResult::Continue
    }

    fn getgid(&mut self, regs: &mut Rv64State, _mem: &mut MMU<SimplePage>) -> SyscallResult {
        regs[Rv64Reg::a0] = 1000;
        SyscallResult::Continue
    }

    fn getegid(&mut self, regs: &mut Rv64State, _mem: &mut MMU<SimplePage>) -> SyscallResult {
        regs[Rv64Reg::a0] = 1000;
        SyscallResult::Continue
    }

    fn brk(&mut self, regs: &mut Rv64State, _mem: &mut MMU<SimplePage>) -> SyscallResult {
        let addr = regs[Rv64Reg::a0];
        if addr < self.heap.start {
            regs[Rv64Reg::a0] = self.heap.start;
        } else if addr > self.heap.end {
            regs[Rv64Reg::a0] = self.heap.end;
        }
        SyscallResult::Continue
    }

    fn mmap(&mut self, regs: &mut Rv64State, mem: &mut MMU<SimplePage>) -> SyscallResult {
        let addr = regs[Rv64Reg::a0];
        let len = regs[Rv64Reg::a1];

        if addr != 0 {
            // Just map at any address that has the required size
            let range = mem.gaps().find(|r| r.size() >= len as usize);
            if let Some(addrs) = range {
                let page = mem.map_memory(addrs.start, len as usize, Perm::READ | Perm::WRITE);
                if page.is_ok() {
                    regs[Rv64Reg::a0] = addrs.start as u64;
                    return SyscallResult::Continue;
                }
            }
            regs[Rv64Reg::a0] = u64::MAX;
            return SyscallResult::Continue;
        } else {
            let page = mem.map_memory(addr as usize, len as usize, Perm::READ | Perm::WRITE);
            if page.is_ok() {
                regs[Rv64Reg::a0] = addr;
                return SyscallResult::Continue;
            }
            regs[Rv64Reg::a0] = u64::MAX;
            return SyscallResult::Continue;
        }
    }
}

fn main() {
    let required_functions: &[u64] = &[
        0x1054c, 0x1056e, 0x1073a, 0x29294, 0x29ce8, 0x47830, 0x47824, 0x28ae6, 0x10a90, 0x28962,
        0x281d2, 0x28fcc, 0x47848, 0x4783c, 0x26c18, 0x26bec, 0x24dfe, 0x24e92, 0x28988, 0x14b5c,
        0x14aa2, 0x223ba,
    ];
    let headless_session = Session::new().expect("Failed to create new session");
    let bv = headless_session
        .load("./test-bins/sum-stdin.bndb")
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
    env.aux.push(AuxVal::Random([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]));
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

    let mut emu = Emulator::new(prog, state);
    emu.add_hook(0x14ac6, store_conditional_hook).expect("Failed to install first hook");
    emu.add_hook(0x223dc, store_conditional_hook2).expect("Failed to install second hook");
    // emu.add_hook(0x29318, compare_hook);
    // This is the it just returns without parsing the auxiliary vectors
    // emu.add_breakpoint(0x294ca);
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
        } else {
            break;
        }
    }
    println!("Stop reason: {:?}", stop_reason);
    println!("Stopped at: {:#x}", emu.curr_pc());

    let mut stdout = emu.get_state_mut().syscalls.take_fd(1).unwrap();
    let message = String::from_utf8(stdout.make_contiguous().to_vec()).unwrap();
    println!("{message}");
}

fn compare_hook(state: &mut dyn State<Reg = Rv64Reg, Endianness = Little>) -> HookStatus {
    let t3 = state.read_reg(Rv64Reg::t3).extend_64();
    println!("t3 is: {:#?}", state.read_reg(Rv64Reg::t3));
    if t3 == 0 {
        HookStatus::Exit
    } else {
        HookStatus::Continue
    }
}

fn store_conditional_hook(state: &mut dyn State<Reg = Rv64Reg, Endianness = Little>) -> HookStatus {
    let mut buf = [0u8; 8];
    let addr = state.read_reg(Rv64Reg::a1).extend_64();
    let value = state.read_reg(Rv64Reg::a4).truncate(4);
    Little::write(value, &mut buf);
    let _ = state.write_mem(addr, &buf[0..4]);
    state.write_reg(Rv64Reg::a2, ILVal::Word(0));
    HookStatus::Goto(0x14aca)
}

fn store_conditional_hook2(state: &mut dyn State<Reg = Rv64Reg, Endianness = Little>) -> HookStatus {
    let mut buf = [0u8; 8];
    let addr = state.read_reg(Rv64Reg::s0).extend_64();
    let value = state.read_reg(Rv64Reg::a4).truncate(4);
    Little::write(value, &mut buf);
    let _ = state.write_mem(addr, &buf[0..4]);
    state.write_reg(Rv64Reg::a3, ILVal::Word(0));
    HookStatus::Goto(0x223e0)
}
