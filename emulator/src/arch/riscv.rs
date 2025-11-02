use crate::arch::Little;
use crate::arch::{FileDescriptor, Intrinsic, RegState, State};
use crate::arch::{Register, SyscallResult};
use crate::emil::ILVal;
use crate::os::linux::LinuxSyscalls;
use from_id::FromId;
use softmew::{MMU, Perm, fault::Fault, page::Page, page::SimplePage};
use std::collections::{HashMap, VecDeque};
use std::ops::{Index, IndexMut, Range};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug)]
pub struct RVIntrinsic(u32);

impl Intrinsic for RVIntrinsic {
    fn parse(
        operation: &binaryninja::low_level_il::operation::Operation<
            '_,
            binaryninja::low_level_il::function::Finalized,
            binaryninja::low_level_il::function::NonSSA,
            binaryninja::low_level_il::operation::Intrinsic,
        >,
    ) -> Result<Self, String> {
        let id = operation.intrinsic();
        match id {
            Some(i) => Ok(Self(i.id.0)),
            None => Err(format!("Intrinsic has invalid id")),
        }
    }
}

pub struct LinuxRV64<S> {
    pub regs: Rv64State,
    pub mem: MMU<SimplePage>,
    pub flag: u64,
    pub conds: [u8; 32],
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
            conds: [0; 32],
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

impl<S: LinuxSyscalls<Rv64State, MMU<SimplePage>>> State<SimplePage> for LinuxRV64<S> {
    type Registers = Rv64State;
    type Endianness = Little;
    type Intrin = RVIntrinsic;

    #[inline]
    fn regs(&mut self) -> &mut Self::Registers {
        &mut self.regs
    }

    #[inline]
    fn mem(&mut self) -> &mut MMU<SimplePage> {
        &mut self.mem
    }

    #[inline]
    fn underlying(&mut self) -> (&mut Self::Registers, &mut MMU<SimplePage>) {
        (&mut self.regs, &mut self.mem)
    }

    #[inline]
    fn get_flag(&self, id: u32) -> bool {
        if id < 32 {
            ((self.flag >> id) & 0b1) != 0
        } else {
            (self.conds[(id - 0x80000000) as usize]) != 0
        }
    }

    fn set_flag(&mut self, val: bool, id: u32) {
        if id < 32 {
            self.flag &= !((val as u64) << id);
            self.flag |= (val as u64) << id;
        } else {
            self.conds[(id - 0x80000000) as usize] = val as u8;
        }
    }

    fn syscall(&mut self, _addr: u64) -> SyscallResult {
        match self.regs[Rv64Reg::a7] {
            0x30 => self.syscalls.faccessat(&mut self.regs, &mut self.mem),
            0x3f => self.syscalls.read(&mut self.regs, &mut self.mem),
            0x40 => self.syscalls.write(&mut self.regs, &mut self.mem),
            0x42 => self.syscalls.writev(&mut self.regs, &mut self.mem),
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
            0xde => self.syscalls.mmap(&mut self.regs, &mut self.mem),
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

    fn intrinsic(&mut self, i: &RVIntrinsic) -> Result<(), Fault> {
        match i.0 {
            26214400 => {
                // This is a memory fence. Just ignore it.
                Ok(())
            }
            _ => unimplemented!("Intrinsic {}", i.0),
        }
    }
}

#[derive(Default, Clone, Copy, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Rv64State {
    gregs: [u64; 32],
}

impl RegState for Rv64State {
    type RegID = Rv64Reg;

    fn read(&self, id: Self::RegID) -> ILVal {
        ILVal::Quad(self[id])
    }

    fn write(&mut self, id: Self::RegID, val: ILVal) {
        self[id] = val.get_quad()
    }

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
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
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
    fn id(&self) -> u32 {
        *self as u32
    }
}

/// Basic linux state for a RV64 machine.
///
/// Implements the basic system calls and will keep track of stdin, stdout, and stderr state.
pub struct RvMachine {
    fds: HashMap<u32, Box<dyn FileDescriptor>>,
    heap: Range<u64>,
}

impl RvMachine {
    /// Create a new machine with initially empty stdin, stdout, and stderr.
    ///
    /// `heap` is the range of addresses that should be used for the heap. Those addresses are used to set return values for
    /// the brk syscall.
    pub fn new(heap: Range<u64>) -> Self {
        let mut map = HashMap::new();
        let stdin: Box<dyn FileDescriptor> = Box::new(VecDeque::<u8>::new());
        let stdout: Box<dyn FileDescriptor> = Box::new(VecDeque::<u8>::new());
        let stderr: Box<dyn FileDescriptor> = Box::new(VecDeque::<u8>::new());
        map.insert(0, stdin);
        map.insert(1, stdout);
        map.insert(2, stderr);
        Self { fds: map, heap }
    }

    pub fn take_fd(&mut self, fd: u32) -> Option<Box<dyn FileDescriptor>> {
        self.fds.remove(&fd)
    }

    pub fn set_stdin<T: FileDescriptor>(&mut self, data: T) -> Option<Box<dyn FileDescriptor>> {
        let stdin = Box::new(data);
        self.fds.insert(0, stdin)
    }

    pub fn get_fd(&self, fd: u32) -> Option<&dyn FileDescriptor> {
        self.fds.get(&fd).map(|f| f.as_ref())
    }

    pub fn get_fd_mut(&mut self, fd: u32) -> Option<&mut dyn FileDescriptor> {
        self.fds.get_mut(&fd).map(|f| f.as_mut())
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
        mem.read_perm(ptr as usize, &mut data)
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

    fn set_tid_address(
        &mut self,
        regs: &mut Rv64State,
        _mem: &mut MMU<SimplePage>,
    ) -> SyscallResult {
        regs[Rv64Reg::a0] = 100;
        SyscallResult::Continue
    }

    fn set_robust_list(
        &mut self,
        regs: &mut Rv64State,
        _mem: &mut MMU<SimplePage>,
    ) -> SyscallResult {
        regs[Rv64Reg::a0] = 0;
        SyscallResult::Continue
    }

    fn uname(&mut self, regs: &mut Rv64State, mem: &mut MMU<SimplePage>) -> SyscallResult {
        let addr = regs[Rv64Reg::a0];
        regs[Rv64Reg::a0] = (-14_i64) as u64;
        if mem.write_perm(addr as usize, b"Linux\x00").is_err() {
            return SyscallResult::Continue;
        }
        if mem
            .write_perm((addr + 65) as usize, b"binja.emu\x00")
            .is_err()
        {
            return SyscallResult::Continue;
        }
        if mem
            .write_perm((addr + 65 * 2) as usize, b"6.0\x00")
            .is_err()
        {
            return SyscallResult::Continue;
        }
        if mem
            .write_perm((addr + 65 * 3) as usize, b"6.0\x00")
            .is_err()
        {
            return SyscallResult::Continue;
        }
        if mem
            .write_perm((addr + 65 * 4) as usize, b"rv64gc\x00")
            .is_err()
        {
            return SyscallResult::Continue;
        }
        if mem
            .write_perm((addr + 65 * 5) as usize, b"binja.emu\x00")
            .is_err()
        {
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
                return SyscallResult::Continue;
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

    fn writev(&mut self, regs: &mut Rv64State, _mem: &mut MMU<SimplePage>) -> SyscallResult {
        let _fd = regs[Rv64Reg::a0];
        let _iov = regs[Rv64Reg::a1];
        let _iocnt = regs[Rv64Reg::a2];
        SyscallResult::Continue
    }
}
