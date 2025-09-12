use crate::arch::{FileDescriptor, State};
use crate::arch::{Register, SyscallResult};
use crate::emil::ILVal;
use crate::emulate::Little;
use from_id::FromId;
use softmew::page::Page;
use softmew::{MMU, fault::Fault, page::SimplePage};

use std::collections::HashMap;
use std::ops::{Index, IndexMut, Range};

pub struct AuxV {
    pub ty: u64,
    pub val: u64,
}

#[derive(Default)]
pub struct Environment {
    pub args: Vec<String>,
    pub env: Vec<String>,
    pub aux: Vec<AuxV>,
}

impl Environment {
    pub fn encode(&self, data: &mut [u8], top: u64) -> Result<u64, ()> {
        data.fill(0);
        let mut current = top;
        let argc = self.args.len();
        let mut len = data.len();
        let mut env_ptrs = Vec::new();
        let mut arg_ptrs = Vec::new();
        for e in &self.env {
            len = len - e.as_bytes().len() - 1;
            current = current - e.as_bytes().len() as u64 - 1;
            data[len..][..e.as_bytes().len()].copy_from_slice(e.as_bytes());
            env_ptrs.push(current);
        }
        for a in &self.args {
            len = len - a.as_bytes().len() - 1;
            current = current - a.as_bytes().len() as u64 - 1;
            data[len..][..a.as_bytes().len()].copy_from_slice(a.as_bytes());
            arg_ptrs.push(current);
        }
        while len % 64 != 0 {
            len -= 1;
            current -= 1;
        }
        for ptr in env_ptrs {
            data[len..][..8].copy_from_slice(&ptr.to_le_bytes());
            len -= 8;
            current -= 8;
        }
        len -= 8;
        current -= 8;
        for ptr in arg_ptrs {
            data[len..][..8].copy_from_slice(&ptr.to_le_bytes());
            len -= 8;
            current -= 8;
        }
        data[len..][..8].copy_from_slice(&argc.to_le_bytes());
        Ok(current)
    }
}

pub struct LinuxRV64<const N: usize> {
    regs: Rv64State,
    temps: [u64; N],
    mem: MMU<SimplePage>,
    flag: u64,
    fds: HashMap<u32, Box<dyn FileDescriptor>>,
    heap: Range<u64>,
}

impl<const N: usize> LinuxRV64<N> {
    pub const ARCH_NAME: &'static str = "rv64gc";

    pub fn new() -> Self {
        let regs = Rv64State::default();
        let mmu = MMU::new();
        Self {
            regs,
            temps: [0; N],
            mem: mmu,
            flag: 0,
            fds: HashMap::new(),
            heap: 0..1,
        }
    }

    #[inline]
    pub fn memory(&self) -> &MMU<SimplePage> {
        &self.mem
    }

    #[inline]
    pub fn memory_mut(&mut self) -> &mut MMU<SimplePage> {
        &mut self.mem
    }

    #[inline]
    pub fn regs(&self) -> &Rv64State {
        &self.regs
    }

    #[inline]
    pub fn regs_mut(&mut self) -> &mut Rv64State {
        &mut self.regs
    }

    #[inline]
    pub fn register_fd(&mut self, fd: u32, file: Box<dyn FileDescriptor>) {
        self.fds.insert(fd, file);
    }

    #[inline]
    pub fn take_fd(&mut self, fd: u32) -> Option<Box<dyn FileDescriptor>> {
        self.fds.remove(&fd)
    }

    #[inline]
    pub fn set_heap(&mut self, base: u64, size: u64) {
        self.heap = base..base + size;
    }
}

impl<const N: usize> State for LinuxRV64<N> {
    type Reg = Rv64Reg;
    type Endianness = Little;

    #[inline(always)]
    fn read_reg(&self, id: Rv64Reg) -> ILVal {
        ILVal::from(self.regs[id])
    }

    #[inline(always)]
    fn write_reg(&mut self, id: Rv64Reg, val: ILVal) {
        self.regs[id] = val.extend_64();
    }

    fn read_temp(&self, idx: usize) -> u64 {
        self.temps[idx]
    }

    fn write_temp(&mut self, idx: usize, val: u64) {
        self.temps[idx] = val;
    }

    fn read_mem(&self, addr: u64, buf: &mut [u8]) -> Result<(), Fault> {
        self.mem.read_perm(addr as usize, buf)
    }

    fn write_mem(&mut self, addr: u64, data: &[u8]) -> Result<(), Fault> {
        self.mem.write_perm(addr as usize, data)
    }

    fn get_flags(&self) -> u64 {
        self.flag
    }

    fn set_flags(&mut self, val: ILVal) {
        self.flag = val.extend_64();
    }

    fn syscall(&mut self) -> SyscallResult {
        match self.regs[Rv64Reg::a7] {
            0x30 => {
                // f access at
                // Not implemented properly right now. Return an error.
                // This is a file does not exist error.
                self.regs[Rv64Reg::a0] = (-2_i64) as u64;
                SyscallResult::Continue
            }
            0x3f => {
                // Read
                let fd = self.regs[Rv64Reg::a0];
                let ptr = self.regs[Rv64Reg::a1] as usize;
                let len = self.regs[Rv64Reg::a2] as usize;
                match self.fds.get_mut(&(fd as u32)) {
                    Some(file) => {
                        let page = self.mem.get_mapping_mut(ptr).unwrap();
                        let start = page.start();
                        let buf = &mut page.as_mut()[ptr - start..][..len];
                        let res = file.read(buf);
                        match res {
                            Ok(b) => self.regs[Rv64Reg::a0] = b as u64,
                            Err(e) => {
                                self.regs[Rv64Reg::a0] = e.raw_os_error().unwrap_or(-9) as u64;
                            }
                        }
                    }
                    None => self.regs[Rv64Reg::a0] = (-9_i64) as u64,
                };
                SyscallResult::Continue
            }
            0x40 => {
                // Write
                let fd = self.regs[Rv64Reg::a0];
                let ptr = self.regs[Rv64Reg::a1];
                let len = self.regs[Rv64Reg::a2];
                let mut data = vec![0; len as usize];
                self.mem
                    .read_perm(ptr as usize, &mut data)
                    .expect("Failed to read message");
                match self.fds.get_mut(&(fd as u32)) {
                    Some(file) => {
                        let res = file.write(&data);
                        match res {
                            Ok(b) => self.regs[Rv64Reg::a0] = b as u64,
                            Err(e) => {
                                self.regs[Rv64Reg::a0] = e.raw_os_error().unwrap_or(-9) as u64;
                            }
                        }
                    }
                    None => self.regs[Rv64Reg::a0] = len,
                }
                SyscallResult::Continue
            }
            0x5d => {
                // Exit
                SyscallResult::Exit
            }
            0x60 => {
                // set_tid_address
                // I think this can be safely ignored for single threaded
                // programs. Just need to return the thread id.
                self.regs[Rv64Reg::a0] = 100;
                SyscallResult::Continue
            }
            0x63 => {
                // set_robust_list
                // This is used for futex implementations. Should be safe to
                // ignore for single threaded programs.
                self.regs[Rv64Reg::a0] = 0;
                SyscallResult::Continue
            }
            0xae => {
                // Get user id
                self.regs[Rv64Reg::a0] = 1000;
                SyscallResult::Continue
            }
            0xaf => {
                // Get effective user id
                self.regs[Rv64Reg::a0] = 1000;
                SyscallResult::Continue
            }
            0xb0 => {
                // Get group id
                self.regs[Rv64Reg::a0] = 1000;
                SyscallResult::Continue
            }
            0xb1 => {
                // Get effective group id
                self.regs[Rv64Reg::a0] = 1000;
                SyscallResult::Continue
            }
            0xd6 => {
                // brk
                let addr = self.regs[Rv64Reg::a0];
                if addr < self.heap.start {
                    self.regs[Rv64Reg::a0] = self.heap.start;
                } else if addr > self.heap.end {
                    self.regs[Rv64Reg::a0] = self.heap.end;
                }
                SyscallResult::Continue
            }
            s => unimplemented!("Syscall 0x{s:X} is not implemented yet"),
        }
    }

    fn save_ret_addr(&mut self, addr: u64) -> Result<(), Fault> {
        self.regs[Rv64Reg::ra] = addr;
        Ok(())
    }

    fn push(&mut self, val: &[u8]) -> Result<(), Fault> {
        let sp = self.regs[Rv64Reg::sp];
        let updated = sp - val.len() as u64;
        self.mem.write_perm(updated as usize, val)?;
        self.regs[Rv64Reg::sp] = updated;
        Ok(())
    }

    fn pop(&mut self, data: &mut [u8]) -> Result<(), Fault> {
        let sp = self.regs[Rv64Reg::sp];
        let updated = sp + data.len() as u64;
        self.mem.read_perm(sp as usize, data)?;
        self.regs[Rv64Reg::sp] = updated;
        Ok(())
    }

    fn intrinsic(&mut self, id: u32) -> Result<(), Fault> {
        match id {
            26214400 => {
                // This is a memory fence. Just ignore it.
                Ok(())
            }
            _ => unimplemented!("Intrinsic {id}"),
        }
    }
}

#[derive(Default, Clone, Copy, Debug)]
pub struct Rv64State {
    gregs: [u64; 32],
}

impl Index<Rv64Reg> for Rv64State {
    type Output = u64;

    fn index(&self, reg: Rv64Reg) -> &u64 {
        match reg {
            Rv64Reg::zero => &0,
            Rv64Reg::ra
            | Rv64Reg::sp
            | Rv64Reg::gp
            | Rv64Reg::tp
            | Rv64Reg::t0
            | Rv64Reg::t1
            | Rv64Reg::t2
            | Rv64Reg::s0
            | Rv64Reg::s1
            | Rv64Reg::a0
            | Rv64Reg::a1
            | Rv64Reg::a2
            | Rv64Reg::a3
            | Rv64Reg::a4
            | Rv64Reg::a5
            | Rv64Reg::a6
            | Rv64Reg::a7
            | Rv64Reg::s2
            | Rv64Reg::s3
            | Rv64Reg::s4
            | Rv64Reg::s5
            | Rv64Reg::s6
            | Rv64Reg::s7
            | Rv64Reg::s8
            | Rv64Reg::s9
            | Rv64Reg::s10
            | Rv64Reg::s11
            | Rv64Reg::t3
            | Rv64Reg::t4
            | Rv64Reg::t5
            | Rv64Reg::t6 => {
                let idx = (reg as u32) as usize;
                unsafe { self.gregs.get_unchecked(idx) }
            }
            _ => panic!("Trying to get floating point register from gpr get"),
        }
    }
}

impl IndexMut<Rv64Reg> for Rv64State {
    fn index_mut(&mut self, reg: Rv64Reg) -> &mut u64 {
        match reg {
            // Setting zero is explicitly a no-op
            Rv64Reg::zero
            | Rv64Reg::ra
            | Rv64Reg::sp
            | Rv64Reg::gp
            | Rv64Reg::tp
            | Rv64Reg::t0
            | Rv64Reg::t1
            | Rv64Reg::t2
            | Rv64Reg::s0
            | Rv64Reg::s1
            | Rv64Reg::a0
            | Rv64Reg::a1
            | Rv64Reg::a2
            | Rv64Reg::a3
            | Rv64Reg::a4
            | Rv64Reg::a5
            | Rv64Reg::a6
            | Rv64Reg::a7
            | Rv64Reg::s2
            | Rv64Reg::s3
            | Rv64Reg::s4
            | Rv64Reg::s5
            | Rv64Reg::s6
            | Rv64Reg::s7
            | Rv64Reg::s8
            | Rv64Reg::s9
            | Rv64Reg::s10
            | Rv64Reg::s11
            | Rv64Reg::t3
            | Rv64Reg::t4
            | Rv64Reg::t5
            | Rv64Reg::t6 => {
                let idx = (reg as u32) as usize;
                unsafe { self.gregs.get_unchecked_mut(idx) }
            }
            _ => panic!("Trying to get floating point register from gpr get"),
        }
    }
}

#[allow(non_camel_case_types)]
#[repr(u32)]
#[derive(FromId, Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rv64Reg {
    zero = 0,
    ra = 1,
    sp = 2,
    gp = 3,
    tp = 4,
    t0 = 5,
    t1 = 6,
    t2 = 7,
    s0 = 8,
    s1 = 9,
    a0 = 10,
    a1 = 11,
    a2 = 12,
    a3 = 13,
    a4 = 14,
    a5 = 15,
    a6 = 16,
    a7 = 17,
    s2 = 18,
    s3 = 19,
    s4 = 20,
    s5 = 21,
    s6 = 22,
    s7 = 23,
    s8 = 24,
    s9 = 25,
    s10 = 26,
    s11 = 27,
    t3 = 28,
    t4 = 29,
    t5 = 30,
    t6 = 31,
    ft0 = 32,
    ft1 = 33,
    ft2 = 34,
    ft3 = 35,
    ft4 = 36,
    ft5 = 37,
    ft6 = 38,
    ft7 = 39,
    fs0 = 40,
    fs1 = 41,
    fa0 = 42,
    fa1 = 43,
    fa2 = 44,
    fa3 = 45,
    fa4 = 46,
    fa5 = 47,
    fa6 = 48,
    fa7 = 49,
    fs2 = 50,
    fs3 = 51,
    fs4 = 52,
    fs5 = 53,
    fs6 = 54,
    fs7 = 55,
    fs8 = 56,
    fs9 = 57,
    fs10 = 58,
    fs11 = 59,
    ft8 = 60,
    ft9 = 61,
    ft10 = 62,
    ft11 = 63,
}

impl std::fmt::Display for Rv64Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", *self)
    }
}

impl Register for Rv64Reg {
    /// Returns [`Self::sp`] as the stack register
    fn stack() -> Self {
        Self::sp
    }
}
