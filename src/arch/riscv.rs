use crate::arch::{RegState, State};
use crate::arch::{Register, SyscallResult};
use crate::emil::ILVal;
use crate::emulate::Little;
use crate::os::linux::LinuxSyscalls;
use from_id::FromId;
use softmew::{MMU, fault::Fault, page::SimplePage};

use std::ops::{Index, IndexMut};

pub struct LinuxRV64<S> {
    pub regs: Rv64State,
    pub mem: MMU<SimplePage>,
    pub flag: u64,
    pub syscalls: S,
}

impl<S> LinuxRV64<S> {
    pub const ARCH_NAME: &'static str = "rv64gc";

    pub fn new(syscalls: S) -> Self {
        let regs = Rv64State::default();
        let mmu = MMU::new();
        Self {
            regs,
            mem: mmu,
            flag: 0,
            syscalls,
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
}

impl<S: LinuxSyscalls<Rv64State, MMU<SimplePage>>> State for LinuxRV64<S> {
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
            0x30 => self.syscalls.faccessat(&mut self.regs, &mut self.mem),
            0x3f => self.syscalls.read(&mut self.regs, &mut self.mem),
            0x40 => self.syscalls.write(&mut self.regs, &mut self.mem),
            0x4e => self.syscalls.readlinkat(&mut self.regs, &mut self.mem),
            0x5d => self.syscalls.exit(&mut self.regs, &mut self.mem),
            0x60 => self.syscalls.set_tid_address(&mut self.regs, &mut self.mem),
            0x63 => self.syscalls.set_robust_list(&mut self.regs, &mut self.mem),
            0x71 => self.syscalls.clock_gettime(&mut self.regs, &mut self.mem),
            0xa0 => self.syscalls.uname(&mut self.regs, &mut self.mem),
            0xae => self.syscalls.getuid(&mut self.regs, &mut self.mem),
            0xaf => self.syscalls.geteuid(&mut self.regs, &mut self.mem),
            0xb0 => self.syscalls.getgid(&mut self.regs, &mut self.mem),
            0xb1 => self.syscalls.getegid(&mut self.regs, &mut self.mem),
            0xd6 => self.syscalls.brk(&mut self.regs, &mut self.mem),
            0x105 => self.syscalls.prlimit64(&mut self.regs, &mut self.mem),
            0x116 => self.syscalls.getrandom(&mut self.regs, &mut self.mem),
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

impl RegState for Rv64State {
    fn set_syscall_return(&mut self, val: ILVal) {
        self.gregs[(Rv64Reg::a0 as u32) as usize] = val.extend_64();
    }
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
    fn syscall_ret() -> Self {
        Self::a0
    }
}
