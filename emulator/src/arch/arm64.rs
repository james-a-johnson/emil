use crate::arch::{Endian, Little};
use crate::arch::{FileDescriptor, Intrinsic, RegState, Register, State, SyscallResult};
use crate::os::linux::LinuxSyscalls;
use val::{Big, ILVal};
use binaryninja::architecture::{Intrinsic as _, Register as BNReg};
use binaryninja::low_level_il::expression::ExpressionHandler;
use binaryninja::low_level_il::expression::LowLevelILExpressionKind as ExprKind;
use binaryninja::low_level_il::operation::IntrinsicOutput;
use from_id::FromId;
use softmew::page::SimplePage;
use softmew::{MMU, Perm};

use std::collections::{HashMap, VecDeque};
use std::ffi::{CString, OsString};
use std::fs::OpenOptions;
use std::ops::{Index, IndexMut, Range};
use std::os::unix::ffi::OsStringExt;
use std::path::PathBuf;

#[derive(Clone, Copy, Debug)]
pub enum ArmIntrinsic {
    /// Data cache operation.
    Dc,
    WriteMSR(Arm64Reg, u32),
    ReadMSR(Arm64Reg, u32),
    Clz(Arm64Reg, Arm64Reg),
    /// Reverses bit order of a register
    Rbit(Arm64Reg, Arm64Reg),
    Rev(Arm64Reg, Arm64Reg),
    /// (Destnation register, Address register).
    Ldxr(Arm64Reg, Arm64Reg),
    /// (Destination register, Value Register, Address register).
    Stxr(Arm64Reg, Arm64Reg, Arm64Reg),
    Dmb,
    BtiHint,
}

impl Intrinsic for ArmIntrinsic {
    fn parse(
        intrinsic: &binaryninja::low_level_il::operation::Operation<
            '_,
            binaryninja::low_level_il::function::Finalized,
            binaryninja::low_level_il::function::NonSSA,
            binaryninja::low_level_il::operation::Intrinsic,
        >,
    ) -> Result<Self, String> {
        let intrin = intrinsic
            .intrinsic()
            .expect("This is an intrinsic instruction");
        let intrinsic_name = intrin.name();
        // Match on the name of the intrinsic since it shouldn't change between versions of
        // binary ninja and the API.
        match intrinsic_name.as_ref() {
            "__dc" => Ok(Self::Dc),
            "__dmb" => Ok(Self::Dmb),
            // TODO: Fix this name
            "btihint" => Ok(Self::BtiHint),
            "_CountLeadingZeros" => {
                let dest_reg = get_reg_from_outputs(intrinsic, 0)
                    .map_err(|e| format!("Bad output for reverse: {e}"))?;
                let src_reg = get_reg_from_inputs(intrinsic, 0)
                    .map_err(|e| format!("Bad source register for reverse: {e}"))?;
                Ok(Self::Clz(dest_reg, src_reg))
            }
            // TODO: Fix this name
            "rev" => {
                let dest_reg = get_reg_from_outputs(intrinsic, 0)
                    .map_err(|e| format!("Bad output for reverse: {e}"))?;
                let src_reg = get_reg_from_inputs(intrinsic, 0)
                    .map_err(|e| format!("Bad source register for reverse: {e}"))?;
                Ok(Self::Rev(dest_reg, src_reg))
            }
            "__rbit" => {
                let dest_reg = get_reg_from_outputs(intrinsic, 0)
                    .map_err(|e| format!("Bad output register for rbit: {e}"))?;
                let src_reg = get_reg_from_inputs(intrinsic, 0)
                    .map_err(|e| format!("Bad source register for rbit: {e}"))?;
                Ok(Self::Rbit(dest_reg, src_reg))
            }
            "__ldaxr" => {
                // ldaxr, load acquire exclusive
                let dest_reg = get_reg_from_outputs(intrinsic, 0)
                    .map_err(|e| format!("Couldn't get register to load into for ldaxr: {e}"))?;
                let source_reg = get_reg_from_inputs(intrinsic, 0)
                    .map_err(|e| format!("Couldn't get source register for ldaxr: {e}"))?;
                Ok(Self::Ldxr(dest_reg, source_reg))
            }
            "__stlxr" => {
                // stxr store exclusive
                let dest_reg = get_reg_from_outputs(intrinsic, 0)
                    .map_err(|e| format!("Bad output reg for stxr: {e}"))?;
                let value_reg = get_reg_from_inputs(intrinsic, 0)
                    .map_err(|e| format!("Failed to get value register to use: {e}"))?;
                let addr_reg = get_reg_from_inputs(intrinsic, 1)
                    .map_err(|e| format!("Failed to get value register to use: {e}"))?;
                Ok(Self::Stxr(dest_reg, value_reg, addr_reg))
            }
            "_ReadMSR" => {
                // Read msr into an architecture register.
                // First element of output array should be a register.
                let outputs = intrinsic.outputs();
                let reg = outputs
                    .get(0)
                    .ok_or(format!("MSR is not writing a register"))?;
                let reg = if let IntrinsicOutput::Reg(r) = reg {
                    Arm64Reg::try_from(r.id().0).unwrap()
                } else {
                    return Err(format!("Can't write msr to a flag"));
                };
                let msr = get_const_from_inputs(intrinsic, 0)
                    .map_err(|e| format!("Failed to get msr for msr read: {e}"))?;
                Ok(Self::ReadMSR(reg, msr as u32))
            }
            "_WriteMSR" => {
                // Write architecture register into system register.
                // All information is in the inputs array. That will have the system register number and then the
                // architecture register ID.
                let sys_id = get_const_from_inputs(intrinsic, 0)
                    .map(|c| c as u32)
                    .map_err(|e| format!("Could not get id of msr to read: {e}"))?;
                let reg = get_reg_from_inputs(intrinsic, 1).map_err(|e| {
                    format!("Failed to get register to write from MSR intrinsic: {e}")
                })?;
                Ok(Self::WriteMSR(reg, sys_id))
            }
            _ => Err(format!("Don't support {intrinsic_name} yet")),
        }
    }
}

fn get_reg_from_outputs(
    op: &binaryninja::low_level_il::operation::Operation<
        '_,
        binaryninja::low_level_il::function::Finalized,
        binaryninja::low_level_il::function::NonSSA,
        binaryninja::low_level_il::operation::Intrinsic,
    >,
    idx: usize,
) -> Result<Arm64Reg, String> {
    let outputs = op.outputs();
    let reg = outputs
        .get(idx)
        .ok_or(format!("Fewer than {idx} outputs"))?;
    let reg = if let IntrinsicOutput::Reg(r) = reg {
        Arm64Reg::try_from(r.id().0).unwrap()
    } else {
        return Err(format!("Output {idx} is a flag"));
    };
    Ok(reg)
}

fn get_reg_from_inputs(
    op: &binaryninja::low_level_il::operation::Operation<
        '_,
        binaryninja::low_level_il::function::Finalized,
        binaryninja::low_level_il::function::NonSSA,
        binaryninja::low_level_il::operation::Intrinsic,
    >,
    idx: usize,
) -> Result<Arm64Reg, String> {
    let inputs = op.inputs().kind();
    let reg = match inputs {
        ExprKind::CallParamSsa(ref p) => {
            if let Some(ExprKind::Reg(r)) = p.param_exprs().get(idx).map(|e| e.kind()) {
                r.source_reg().id().0
            } else {
                return Err(format!("Param {idx} of intrinsic is not a register"));
            }
        }
        _ => return Err(format!("Inputs to intrinsic is not a parameter list")),
    };
    let reg = Arm64Reg::try_from(reg).map_err(|i| format!("{i} is an invalid register id"))?;
    Ok(reg)
}

fn get_const_from_inputs(
    op: &binaryninja::low_level_il::operation::Operation<
        '_,
        binaryninja::low_level_il::function::Finalized,
        binaryninja::low_level_il::function::NonSSA,
        binaryninja::low_level_il::operation::Intrinsic,
    >,
    idx: usize,
) -> Result<u64, String> {
    let inputs = op.inputs().kind();
    let value = match inputs {
        ExprKind::CallParamSsa(ref p) => {
            if let Some(ExprKind::Const(c)) = p.param_exprs().get(idx).map(|e| e.kind()) {
                c.value()
            } else {
                return Err(format!("Param {idx} of intrinsic is not a constant"));
            }
        }
        _ => return Err(format!("Inputs to intrinsic is not a parameter list")),
    };
    Ok(value)
}

/// Number of temporary flags that need to be kept track of.
const NUM_CONDS: usize = 64;

pub struct LinuxArm64 {
    pub regs: Arm64State,
    pub mem: MMU<SimplePage>,
    pub flags: [bool; 64],
    pub conds: [bool; NUM_CONDS],
    pub tpid: u64,
    fds: HashMap<u32, Box<dyn FileDescriptor>>,
    heap: Range<u64>,
    progname: CString,
}

impl LinuxArm64 {
    pub const ARCH_NAME: &'static str = "aarch64";

    pub fn new(name: impl Into<CString>, heap: Range<u64>) -> Self {
        let regs = Arm64State::default();
        let mmu = MMU::new();
        let mut map = HashMap::new();
        let stdin: Box<dyn FileDescriptor> = Box::new(VecDeque::<u8>::new());
        let stdout: Box<dyn FileDescriptor> = Box::new(VecDeque::<u8>::new());
        let stderr: Box<dyn FileDescriptor> = Box::new(VecDeque::<u8>::new());
        map.insert(0, stdin);
        map.insert(1, stdout);
        map.insert(2, stderr);
        Self {
            fds: map,
            heap,
            progname: name.into(),
            regs,
            mem: mmu,
            flags: [false; 64],
            conds: [false; NUM_CONDS],
            tpid: 0,
        }
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

    #[inline]
    pub fn memory(&self) -> &MMU<SimplePage> {
        &self.mem
    }

    #[inline]
    pub fn memory_mut(&mut self) -> &mut MMU<SimplePage> {
        &mut self.mem
    }

    #[inline]
    pub fn regs(&self) -> &Arm64State {
        &self.regs
    }

    #[inline]
    pub fn regs_mut(&mut self) -> &mut Arm64State {
        &mut self.regs
    }
}

macro_rules! syscalls {
    ($handler:ident, $sys_no:ident, $(($num:literal, $name:ident)),*) => {
        match $sys_no {
            $($num => $handler.$name(),)*
            no => unimplemented!("Syscall {no:#x} is not implemented"),
        }
    };
}

impl State<SimplePage> for LinuxArm64 {
    type Registers = Arm64State;
    type Endianness = Little;
    type Intrin = ArmIntrinsic;

    fn regs(&mut self) -> &mut Self::Registers {
        &mut self.regs
    }

    fn mem(&mut self) -> &mut MMU<SimplePage> {
        &mut self.mem
    }

    fn underlying(&mut self) -> (&mut Self::Registers, &mut MMU<SimplePage>) {
        (&mut self.regs, &mut self.mem)
    }

    fn get_flag(&self, id: u32) -> bool {
        if id < 32 {
            self.flags[id as usize]
        } else {
            self.conds[(id - 0x80000000) as usize]
        }
    }

    fn set_flag(&mut self, val: bool, id: u32) {
        if id < 32 {
            self.flags[id as usize] = val;
        } else {
            self.conds[(id - 0x80000000) as usize] = val;
        }
    }

    fn save_ret_addr(&mut self, addr: u64) -> Result<(), softmew::fault::Fault> {
        self.regs[Arm64Reg::lr] = addr;
        Ok(())
    }

    fn push(&mut self, val: &[u8]) -> Result<(), softmew::fault::Fault> {
        let mut sp = self.regs[Arm64Reg::sp];
        sp -= val.len() as u64;
        self.regs[Arm64Reg::sp] = sp;
        self.mem.write_perm(sp as usize, val)
    }

    fn pop(&mut self, data: &mut [u8]) -> Result<(), softmew::fault::Fault> {
        let sp = self.regs[Arm64Reg::sp];
        self.regs[Arm64Reg::sp] = sp - data.len() as u64;
        self.mem.read_perm(sp as usize, data)
    }

    fn intrinsic(&mut self, intrin: &ArmIntrinsic) -> Result<(), softmew::fault::Fault> {
        match intrin {
            ArmIntrinsic::Dc => Ok(()),
            ArmIntrinsic::Dmb => Ok(()),
            ArmIntrinsic::BtiHint => Ok(()),
            ArmIntrinsic::Rev(dest, src) => {
                let val = self.regs.read(*src);
                self.regs.write(*dest, &val.byte_rev());
                Ok(())
            }
            ArmIntrinsic::Rbit(dest, src) => {
                let val = self.regs.read(*src);
                self.regs.write(*dest, &val.bit_rev());
                Ok(())
            }
            ArmIntrinsic::Clz(dest, src) => {
                let val = self.regs.read(*src);
                self.regs.write(*dest, &val.leading_zeros());
                Ok(())
            }
            ArmIntrinsic::Ldxr(dest, addr) => {
                let addr = self.regs.read(*addr).extend_64() as usize;
                let mut buf = [0u8; 8];
                self.mem.read_perm(addr, &mut buf[0..dest.size()])?;
                let val = Little::read(&buf[0..dest.size()]);
                self.regs.write(*dest, &val);
                Ok(())
            }
            ArmIntrinsic::Stxr(dest, value, addr) => {
                let addr = self.regs.read(*addr).extend_64() as usize;
                let value = self.regs.read(*value);
                let buf = self
                    .mem
                    .get_slice_mut(addr..addr + value.size(), Perm::WRITE)?;
                Little::write(&value, buf);
                self.regs.write(*dest, &ILVal::Word(0));
                Ok(())
            }
            ArmIntrinsic::ReadMSR(reg, msr) => {
                match msr {
                    0xd807 => {
                        // DCZID_EL0 system register
                        self.regs.write(*reg, &ILVal::Quad(0b10000));
                        Ok(())
                    }
                    0xc000 => {
                        // MIDR_EL1, Main ID Register
                        self.regs
                            .write(*reg, &ILVal::Quad(0b00000000_0000_1111_000000000000_0000));
                        Ok(())
                    }
                    0xde82 => {
                        // TPIDR_EL0, Thread ID Register
                        self.regs[*reg] = self.tpid;
                        Ok(())
                    }
                    x => panic!("Implement reading msr {x:#x}"),
                }
            }
            ArmIntrinsic::WriteMSR(reg, msr) => {
                match msr {
                    0xde82 => {
                        // TPIDR_EL0, Thread ID Register
                        self.tpid = self.regs[*reg];
                        Ok(())
                    }
                    x => panic!("Implement writing msr {x:#x}"),
                }
            }
        }
    }

    fn syscall(&mut self, _addr: u64) -> super::SyscallResult {
        let syscall_no = self.regs.gregs[8] as u32;
        syscalls!(
            self,
            syscall_no,
            (0x38, openat),
            (0x39, close),
            (0x3f, read),
            (0x40, write),
            (0x4e, readlinkat),
            (0x4f, newfstatat),
            (0x5d, exit),
            (0x5e, exit_group),
            (0x60, set_tid_address),
            (0x62, futex),
            (0x63, set_robust_list),
            (0xae, getuid),
            (0xa0, uname),
            (0xaf, geteuid),
            (0xb0, getgid),
            (0xb1, getegid),
            (0xd6, brk),
            (0xd7, munmap),
            (0xde, mmap),
            (0xe2, mprotect),
            (0x105, prlimit64),
            (0x116, getrandom),
            (0x125, rseq)
        )
    }
}

impl LinuxSyscalls for LinuxArm64 {
    fn set_syscall_return(&mut self, val: ILVal) {
        self.regs[Arm64Reg::x0] = val.extend_64()
    }

    fn read(&mut self) -> SyscallResult {
        let fd = self.regs[Arm64Reg::x0];
        let ptr = self.regs[Arm64Reg::x1] as usize;
        let len = self.regs[Arm64Reg::x2] as usize;
        let data = self
            .mem
            .get_slice_mut(ptr..ptr + len, Perm::WRITE)
            .expect("Reading to invalid memory");
        match self.fds.get_mut(&(fd as u32)) {
            Some(file) => {
                let res = file.read(data);
                match res {
                    Ok(b) => {
                        self.regs[Arm64Reg::x0] = b as u64;
                    }
                    Err(e) => {
                        self.regs[Arm64Reg::x0] = e.raw_os_error().unwrap_or(-9) as u64;
                    }
                }
            }
            None => self.regs[Arm64Reg::x0] = (-9_i64) as u64,
        };
        SyscallResult::Continue
    }

    fn write(&mut self) -> SyscallResult {
        let fd = self.regs[Arm64Reg::x0];
        let ptr = self.regs[Arm64Reg::x1] as usize;
        let len = self.regs[Arm64Reg::x2] as usize;
        let data = self
            .mem
            .get_slice(ptr..ptr + len, Perm::READ)
            .expect("Failed to read data");
        match self.fds.get_mut(&(fd as u32)) {
            Some(file) => {
                let res = file.write(&data);
                match res {
                    Ok(b) => self.regs[Arm64Reg::x0] = b as u64,
                    Err(e) => {
                        self.regs[Arm64Reg::x0] = e.raw_os_error().unwrap_or(-9) as u64;
                    }
                }
            }
            None => self.regs[Arm64Reg::x0] = len as u64,
        }
        SyscallResult::Continue
    }

    fn set_tid_address(&mut self) -> SyscallResult {
        self.regs[Arm64Reg::x0] = 100;
        SyscallResult::Continue
    }

    fn set_robust_list(&mut self) -> SyscallResult {
        self.regs[Arm64Reg::x0] = 0;
        SyscallResult::Continue
    }

    fn futex(&mut self) -> SyscallResult {
        self.regs[Arm64Reg::x0] = 0;
        SyscallResult::Continue
    }

    fn getrandom(&mut self) -> SyscallResult {
        let buf = self.regs[Arm64Reg::x0] as usize;
        let len = self.regs[Arm64Reg::x1] as usize;
        let buffer = match self.mem.get_slice_mut(buf..buf + len, Perm::WRITE) {
            Ok(s) => s,
            Err(_) => {
                self.regs[Arm64Reg::x0] = (-14_i64) as u64;
                return SyscallResult::Continue;
            }
        };
        buffer.fill(0xaa);
        self.regs[Arm64Reg::x0] = len as u64;
        SyscallResult::Continue
    }

    fn uname(&mut self) -> SyscallResult {
        let addr = self.regs[Arm64Reg::x0];
        self.regs[Arm64Reg::x0] = (-14_i64) as u64;
        if self.mem.write_perm(addr as usize, b"Linux\x00").is_err() {
            return SyscallResult::Continue;
        }
        if self
            .mem
            .write_perm((addr + 65) as usize, b"binja-emu\x00")
            .is_err()
        {
            return SyscallResult::Continue;
        }
        if self
            .mem
            .write_perm((addr + 65 * 2) as usize, b"6.16.3-76061603-generic\x00")
            .is_err()
        {
            return SyscallResult::Continue;
        }
        if self
            .mem
            .write_perm(
                (addr + 65 * 3) as usize,
                b"#202508231538~1758561135~22.04~171c8de\x00",
            )
            .is_err()
        {
            return SyscallResult::Continue;
        }
        if self
            .mem
            .write_perm((addr + 65 * 4) as usize, b"aarch64\x00")
            .is_err()
        {
            return SyscallResult::Continue;
        }
        if self
            .mem
            .write_perm((addr + 65 * 5) as usize, b"binja.emu\x00")
            .is_err()
        {
            return SyscallResult::Continue;
        }
        self.regs[Arm64Reg::x0] = 0;
        SyscallResult::Continue
    }

    fn getuid(&mut self) -> SyscallResult {
        self.regs[Arm64Reg::x0] = 1000;
        SyscallResult::Continue
    }

    fn geteuid(&mut self) -> SyscallResult {
        self.regs[Arm64Reg::x0] = 1000;
        SyscallResult::Continue
    }

    fn getgid(&mut self) -> SyscallResult {
        self.regs[Arm64Reg::x0] = 1000;
        SyscallResult::Continue
    }

    fn getegid(&mut self) -> SyscallResult {
        self.regs[Arm64Reg::x0] = 1000;
        SyscallResult::Continue
    }

    fn brk(&mut self) -> SyscallResult {
        let addr = self.regs[Arm64Reg::x0];
        if addr < self.heap.start {
            self.regs[Arm64Reg::x0] = self.heap.start;
        } else if addr > self.heap.end {
            self.regs[Arm64Reg::x0] = self.heap.end;
        }
        SyscallResult::Continue
    }

    fn mmap(&mut self) -> SyscallResult {
        let addr = self.regs[Arm64Reg::x0];
        let len = self.regs[Arm64Reg::x1];

        if addr == 0 {
            // Just map at any address that has the required size
            let range = self.mem.gaps().find(|r| r.size() >= len as usize);
            if let Some(addrs) = range {
                let page = self
                    .mem
                    .map_memory(addrs.start, len as usize, Perm::READ | Perm::WRITE);
                if page.is_ok() {
                    self.regs[Arm64Reg::x0] = addrs.start as u64;
                    return SyscallResult::Continue;
                }
            }
            self.regs[Arm64Reg::x0] = u64::MAX;
            return SyscallResult::Continue;
        } else {
            let page = self
                .mem
                .map_memory(addr as usize, len as usize, Perm::READ | Perm::WRITE);
            if page.is_ok() {
                self.regs[Arm64Reg::x0] = addr;
                return SyscallResult::Continue;
            }
            self.regs[Arm64Reg::x0] = u64::MAX;
            return SyscallResult::Continue;
        }
    }

    fn mprotect(&mut self) -> SyscallResult {
        self.regs[Arm64Reg::x0] = 0;
        SyscallResult::Continue
    }

    fn writev(&mut self) -> SyscallResult {
        let _fd = self.regs[Arm64Reg::x0];
        let _iov = self.regs[Arm64Reg::x1];
        let _iocnt = self.regs[Arm64Reg::x2];
        SyscallResult::Continue
    }

    fn readlinkat(&mut self) -> SyscallResult {
        let mut path_addr = self.regs[Arm64Reg::x1];
        let mut path = Vec::new();
        let mut buf = [0u8];
        let bufsize = self.regs[Arm64Reg::x2] as usize;
        let copy_size = bufsize.min(self.progname.count_bytes());
        let link_buf = self.regs[Arm64Reg::x2];
        loop {
            if self.mem.read_perm(path_addr as usize, &mut buf).is_err() {
                self.regs[Arm64Reg::x0] = (-14_i64) as u64;
                return SyscallResult::Continue;
            }
            if buf[0] == 0 {
                break;
            }
            path.push(buf[0]);
            path_addr += 1;
        }
        match <Vec<u8> as AsRef<[u8]>>::as_ref(&path) {
            b"/proc/self/exe" => {
                match self
                    .mem
                    .write_perm(link_buf as usize, &self.progname.as_bytes()[..copy_size])
                {
                    Ok(_) => self.regs[Arm64Reg::x0] = copy_size as u64,
                    Err(_) => self.regs[Arm64Reg::x0] = (-14_i16) as u64,
                };
            }
            _ => self.regs[Arm64Reg::x0] = (-2_i64) as u64,
        }
        SyscallResult::Continue
    }

    fn openat(&mut self) -> SyscallResult {
        let mut path_addr = self.regs[Arm64Reg::x1];
        let options = self.regs[Arm64Reg::x2] & 0xffffffff;
        let mut path = Vec::new();
        let mut buf = [0u8];
        loop {
            if self.mem.read_perm(path_addr as usize, &mut buf).is_err() {
                self.regs[Arm64Reg::x0] = (-14_i64) as u64;
                return SyscallResult::Continue;
            }
            if buf[0] == 0 {
                break;
            }
            path.push(buf[0]);
            path_addr += 1;
        }

        let string = OsString::from_vec(path);
        let path = PathBuf::from(string);

        let mut open_options = OpenOptions::new();
        match options & 0b11 {
            0 => open_options.read(true),
            1 => open_options.write(true),
            2 => open_options.read(true).write(true),
            _ => panic!("Invalid open options"),
        };

        let path = path.canonicalize();
        match path {
            Ok(p) => match open_options.open(p) {
                Ok(f) => {
                    let fd: Box<dyn FileDescriptor> = Box::new(f);
                    let num = self.fds.len();
                    self.fds.insert(num.try_into().unwrap(), fd);
                    self.regs[Arm64Reg::x0] = num as u64;
                }
                Err(e) => {
                    let errno = e.raw_os_error().unwrap_or(-2);
                    self.regs[Arm64Reg::x0] = errno as i64 as u64;
                }
            },
            Err(e) => {
                let errno = e.raw_os_error().unwrap_or(-2);
                self.regs[Arm64Reg::x0] = errno as i64 as u64;
            }
        };

        SyscallResult::Continue
    }

    fn close(&mut self) -> SyscallResult {
        let fd = self.regs[Arm64Reg::x0] as u32;
        if self.fds.contains_key(&fd) {
            // Don't actually close here because user of the emulator might want to get the file and look at it
            // themselves.
            self.regs[Arm64Reg::x0] = 0;
        } else {
            self.regs[Arm64Reg::x0] = (-77_i64) as u64;
        }
        SyscallResult::Continue
    }

    fn newfstatat(&mut self) -> SyscallResult {
        self.regs[Arm64Reg::x0] = (-2_i64) as u64;
        SyscallResult::Continue
    }
}

#[derive(Default, Clone, Copy, Debug)]
pub struct Arm64State {
    gregs: [u64; 32],
    neon: [u128; 32],
    syscall_info: u64,
}

impl RegState for Arm64State {
    type RegID = Arm64Reg;

    #[inline]
    fn read(&self, id: Self::RegID) -> ILVal {
        self.get(id)
    }

    fn write(&mut self, id: Self::RegID, value: &ILVal) {
        match id {
            Arm64Reg::w0 => self.gregs[0] = value.to_u32() as u64,
            Arm64Reg::w1 => self.gregs[1] = value.to_u32() as u64,
            Arm64Reg::w2 => self.gregs[2] = value.to_u32() as u64,
            Arm64Reg::w3 => self.gregs[3] = value.to_u32() as u64,
            Arm64Reg::w4 => self.gregs[4] = value.to_u32() as u64,
            Arm64Reg::w5 => self.gregs[5] = value.to_u32() as u64,
            Arm64Reg::w6 => self.gregs[6] = value.to_u32() as u64,
            Arm64Reg::w7 => self.gregs[7] = value.to_u32() as u64,
            Arm64Reg::w8 => self.gregs[8] = value.to_u32() as u64,
            Arm64Reg::w9 => self.gregs[9] = value.to_u32() as u64,
            Arm64Reg::w10 => self.gregs[10] = value.to_u32() as u64,
            Arm64Reg::w11 => self.gregs[11] = value.to_u32() as u64,
            Arm64Reg::w12 => self.gregs[12] = value.to_u32() as u64,
            Arm64Reg::w13 => self.gregs[13] = value.to_u32() as u64,
            Arm64Reg::w14 => self.gregs[14] = value.to_u32() as u64,
            Arm64Reg::w15 => self.gregs[15] = value.to_u32() as u64,
            Arm64Reg::w16 => self.gregs[16] = value.to_u32() as u64,
            Arm64Reg::w17 => self.gregs[17] = value.to_u32() as u64,
            Arm64Reg::w18 => self.gregs[18] = value.to_u32() as u64,
            Arm64Reg::w19 => self.gregs[19] = value.to_u32() as u64,
            Arm64Reg::w20 => self.gregs[20] = value.to_u32() as u64,
            Arm64Reg::w21 => self.gregs[21] = value.to_u32() as u64,
            Arm64Reg::w22 => self.gregs[22] = value.to_u32() as u64,
            Arm64Reg::w23 => self.gregs[23] = value.to_u32() as u64,
            Arm64Reg::w24 => self.gregs[24] = value.to_u32() as u64,
            Arm64Reg::w25 => self.gregs[25] = value.to_u32() as u64,
            Arm64Reg::w26 => self.gregs[26] = value.to_u32() as u64,
            Arm64Reg::w27 => self.gregs[27] = value.to_u32() as u64,
            Arm64Reg::w28 => self.gregs[28] = value.to_u32() as u64,
            Arm64Reg::w29 => self.gregs[29] = value.to_u32() as u64,
            Arm64Reg::w30 => self.gregs[30] = value.to_u32() as u64,
            Arm64Reg::wsp => self.gregs[31] = value.to_u32() as u64,
            Arm64Reg::x0 => self.gregs[0] = value.extend_64(),
            Arm64Reg::x1 => self.gregs[1] = value.extend_64(),
            Arm64Reg::x2 => self.gregs[2] = value.extend_64(),
            Arm64Reg::x3 => self.gregs[3] = value.extend_64(),
            Arm64Reg::x4 => self.gregs[4] = value.extend_64(),
            Arm64Reg::x5 => self.gregs[5] = value.extend_64(),
            Arm64Reg::x6 => self.gregs[6] = value.extend_64(),
            Arm64Reg::x7 => self.gregs[7] = value.extend_64(),
            Arm64Reg::x8 => self.gregs[8] = value.extend_64(),
            Arm64Reg::x9 => self.gregs[9] = value.extend_64(),
            Arm64Reg::x10 => self.gregs[10] = value.extend_64(),
            Arm64Reg::x11 => self.gregs[11] = value.extend_64(),
            Arm64Reg::x12 => self.gregs[12] = value.extend_64(),
            Arm64Reg::x13 => self.gregs[13] = value.extend_64(),
            Arm64Reg::x14 => self.gregs[14] = value.extend_64(),
            Arm64Reg::x15 => self.gregs[15] = value.extend_64(),
            Arm64Reg::x16 => self.gregs[16] = value.extend_64(),
            Arm64Reg::x17 => self.gregs[17] = value.extend_64(),
            Arm64Reg::x18 => self.gregs[18] = value.extend_64(),
            Arm64Reg::x19 => self.gregs[19] = value.extend_64(),
            Arm64Reg::x20 => self.gregs[20] = value.extend_64(),
            Arm64Reg::x21 => self.gregs[21] = value.extend_64(),
            Arm64Reg::x22 => self.gregs[22] = value.extend_64(),
            Arm64Reg::x23 => self.gregs[23] = value.extend_64(),
            Arm64Reg::x24 => self.gregs[24] = value.extend_64(),
            Arm64Reg::x25 => self.gregs[25] = value.extend_64(),
            Arm64Reg::x26 => self.gregs[26] = value.extend_64(),
            Arm64Reg::x27 => self.gregs[27] = value.extend_64(),
            Arm64Reg::x28 => self.gregs[28] = value.extend_64(),
            Arm64Reg::fp => self.gregs[29] = value.extend_64(),
            Arm64Reg::lr => self.gregs[30] = value.extend_64(),
            Arm64Reg::sp => self.gregs[31] = value.extend_64(),
            Arm64Reg::syscall_info => self.syscall_info = value.extend_64(),
            Arm64Reg::d0 => self.neon[0] = value.get_quad() as u128,
            Arm64Reg::d1 => self.neon[1] = value.get_quad() as u128,
            Arm64Reg::d2 => self.neon[2] = value.get_quad() as u128,
            Arm64Reg::d3 => self.neon[3] = value.get_quad() as u128,
            Arm64Reg::d4 => self.neon[4] = value.get_quad() as u128,
            Arm64Reg::d5 => self.neon[5] = value.get_quad() as u128,
            Arm64Reg::d6 => self.neon[6] = value.get_quad() as u128,
            Arm64Reg::d7 => self.neon[7] = value.get_quad() as u128,
            Arm64Reg::d8 => self.neon[8] = value.get_quad() as u128,
            Arm64Reg::d9 => self.neon[9] = value.get_quad() as u128,
            Arm64Reg::d10 => self.neon[10] = value.get_quad() as u128,
            Arm64Reg::d11 => self.neon[11] = value.get_quad() as u128,
            Arm64Reg::d12 => self.neon[12] = value.get_quad() as u128,
            Arm64Reg::d13 => self.neon[13] = value.get_quad() as u128,
            Arm64Reg::d14 => self.neon[14] = value.get_quad() as u128,
            Arm64Reg::d15 => self.neon[15] = value.get_quad() as u128,
            Arm64Reg::d16 => self.neon[16] = value.get_quad() as u128,
            Arm64Reg::d17 => self.neon[17] = value.get_quad() as u128,
            Arm64Reg::d18 => self.neon[18] = value.get_quad() as u128,
            Arm64Reg::d19 => self.neon[19] = value.get_quad() as u128,
            Arm64Reg::d20 => self.neon[20] = value.get_quad() as u128,
            Arm64Reg::d21 => self.neon[21] = value.get_quad() as u128,
            Arm64Reg::d22 => self.neon[22] = value.get_quad() as u128,
            Arm64Reg::d23 => self.neon[23] = value.get_quad() as u128,
            Arm64Reg::d24 => self.neon[24] = value.get_quad() as u128,
            Arm64Reg::d25 => self.neon[25] = value.get_quad() as u128,
            Arm64Reg::d26 => self.neon[26] = value.get_quad() as u128,
            Arm64Reg::d27 => self.neon[27] = value.get_quad() as u128,
            Arm64Reg::d28 => self.neon[28] = value.get_quad() as u128,
            Arm64Reg::d29 => self.neon[29] = value.get_quad() as u128,
            Arm64Reg::d30 => self.neon[30] = value.get_quad() as u128,
            Arm64Reg::d31 => self.neon[31] = value.get_quad() as u128,
            Arm64Reg::s0 => {
                self.neon[0] &= 0xffffffff_u128;
                self.neon[0] |= value.get_word() as u32 as u128;
            }
            Arm64Reg::s1 => {
                self.neon[0] &= 0xffffffff_u128 << 32;
                self.neon[0] |= (value.get_word() as u32 as u128) << 32;
            }
            Arm64Reg::s2 => {
                self.neon[1] &= 0xffffffff_u128;
                self.neon[1] |= value.get_word() as u32 as u128;
            }
            Arm64Reg::s3 => {
                self.neon[1] &= 0xffffffff_u128 << 32;
                self.neon[1] |= (value.get_word() as u32 as u128) << 32;
            }
            Arm64Reg::s4 => {
                self.neon[2] &= 0xffffffff_u128;
                self.neon[2] |= value.get_word() as u32 as u128;
            }
            Arm64Reg::s5 => {
                self.neon[2] &= 0xffffffff_u128 << 32;
                self.neon[2] |= (value.get_word() as u32 as u128) << 32;
            }
            Arm64Reg::s6 => {
                self.neon[3] &= 0xffffffff_u128;
                self.neon[3] |= value.get_word() as u32 as u128;
            }
            Arm64Reg::s7 => {
                self.neon[3] &= 0xffffffff_u128 << 32;
                self.neon[3] |= (value.get_word() as u32 as u128) << 32;
            }
            Arm64Reg::s8 => {
                self.neon[4] &= 0xffffffff_u128;
                self.neon[4] |= value.get_word() as u32 as u128;
            }
            Arm64Reg::s9 => {
                self.neon[4] &= 0xffffffff_u128 << 32;
                self.neon[4] |= (value.get_word() as u32 as u128) << 32;
            }
            Arm64Reg::s10 => {
                self.neon[5] &= 0xffffffff_u128;
                self.neon[5] |= value.get_word() as u32 as u128;
            }
            Arm64Reg::s11 => {
                self.neon[5] &= 0xffffffff_u128 << 32;
                self.neon[5] |= (value.get_word() as u32 as u128) << 32;
            }
            Arm64Reg::s12 => {
                self.neon[6] &= 0xffffffff_u128;
                self.neon[6] |= value.get_word() as u32 as u128;
            }
            Arm64Reg::s13 => {
                self.neon[6] &= 0xffffffff_u128 << 32;
                self.neon[6] |= (value.get_word() as u32 as u128) << 32;
            }
            Arm64Reg::s14 => {
                self.neon[7] &= 0xffffffff_u128;
                self.neon[7] |= value.get_word() as u32 as u128;
            }
            Arm64Reg::s15 => {
                self.neon[7] &= 0xffffffff_u128 << 32;
                self.neon[7] |= (value.get_word() as u32 as u128) << 32;
            }
            Arm64Reg::s16 => {
                self.neon[8] &= 0xffffffff_u128;
                self.neon[8] |= value.get_word() as u32 as u128;
            }
            Arm64Reg::s17 => {
                self.neon[8] &= 0xffffffff_u128 << 32;
                self.neon[8] |= (value.get_word() as u32 as u128) << 32;
            }
            Arm64Reg::s18 => {
                self.neon[9] &= 0xffffffff_u128;
                self.neon[9] |= value.get_word() as u32 as u128;
            }
            Arm64Reg::s19 => {
                self.neon[9] &= 0xffffffff_u128 << 32;
                self.neon[9] |= (value.get_word() as u32 as u128) << 32;
            }
            Arm64Reg::s20 => {
                self.neon[10] &= 0xffffffff_u128;
                self.neon[10] |= value.get_word() as u32 as u128;
            }
            Arm64Reg::s21 => {
                self.neon[10] &= 0xffffffff_u128 << 32;
                self.neon[10] |= (value.get_word() as u32 as u128) << 32;
            }
            Arm64Reg::s22 => {
                self.neon[11] &= 0xffffffff_u128;
                self.neon[11] |= value.get_word() as u32 as u128;
            }
            Arm64Reg::s23 => {
                self.neon[11] &= 0xffffffff_u128 << 32;
                self.neon[11] |= (value.get_word() as u32 as u128) << 32;
            }
            Arm64Reg::s24 => {
                self.neon[12] &= 0xffffffff_u128;
                self.neon[12] |= value.get_word() as u32 as u128;
            }
            Arm64Reg::s25 => {
                self.neon[12] &= 0xffffffff_u128 << 32;
                self.neon[12] |= (value.get_word() as u32 as u128) << 32;
            }
            Arm64Reg::s26 => {
                self.neon[13] &= 0xffffffff_u128;
                self.neon[13] |= value.get_word() as u32 as u128;
            }
            Arm64Reg::s27 => {
                self.neon[13] &= 0xffffffff_u128 << 32;
                self.neon[13] |= (value.get_word() as u32 as u128) << 32;
            }
            Arm64Reg::s28 => {
                self.neon[14] &= 0xffffffff_u128;
                self.neon[14] |= value.get_word() as u32 as u128;
            }
            Arm64Reg::s29 => {
                self.neon[14] &= 0xffffffff_u128 << 32;
                self.neon[14] |= (value.get_word() as u32 as u128) << 32;
            }
            Arm64Reg::s30 => {
                self.neon[15] &= 0xffffffff_u128;
                self.neon[15] |= value.get_word() as u32 as u128;
            }
            Arm64Reg::s31 => {
                self.neon[15] &= 0xffffffff_u128 << 32;
                self.neon[15] |= (value.get_word() as u32 as u128) << 32;
            }
            Arm64Reg::q0 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[0] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q1 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[1] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q2 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[2] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q3 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[3] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q4 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[4] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q5 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[5] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q6 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[6] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q7 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[7] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q8 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[8] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q9 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[9] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q10 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[10] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q11 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[11] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q12 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[12] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q13 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[13] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q14 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[14] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q15 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[15] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q16 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[16] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q17 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[17] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q18 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[18] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q19 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[19] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q20 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[20] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q21 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[21] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q22 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[22] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q23 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[23] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q24 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[24] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q25 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[25] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q26 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[26] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q27 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[27] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q28 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[28] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q29 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[29] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q30 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[30] = u128::from_le_bytes(reg);
            }
            Arm64Reg::q31 => {
                let reg: [u8; 16] = value
                    .get_big()
                    .bytes()
                    .try_into()
                    .expect("Needs to be 16 byte array");
                self.neon[31] = u128::from_le_bytes(reg);
            }
            Arm64Reg::v0b0 => {
                self.neon[0] &= !(0xff_u128 << (8 * 0));
                self.neon[0] |= (value.get_byte() as u128) << (8 * 0);
            }
            Arm64Reg::v0b1 => {
                self.neon[0] &= !(0xff_u128 << (1 * 8));
                self.neon[0] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v0b2 => {
                self.neon[0] &= !(0xff_u128 << (2 * 8));
                self.neon[0] |= !(value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v0b3 => {
                self.neon[0] &= !(0xff_u128 << (3 * 8));
                self.neon[0] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v0b4 => {
                self.neon[0] &= !(0xff_u128 << (4 * 8));
                self.neon[0] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v0b5 => {
                self.neon[0] &= !(0xff_u128 << (5 * 8));
                self.neon[0] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v0b6 => {
                self.neon[0] &= !(0xff_u128 << (6 * 8));
                self.neon[0] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v0b7 => {
                self.neon[0] &= !(0xff_u128 << (7 * 8));
                self.neon[0] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v0b8 => {
                self.neon[0] &= !(0xff_u128 << (8 * 8));
                self.neon[0] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v0b9 => {
                self.neon[0] &= !(0xff_u128 << (9 * 8));
                self.neon[0] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v0b10 => {
                self.neon[0] &= !(0xff_u128 << (10 * 8));
                self.neon[0] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v0b11 => {
                self.neon[0] &= !(0xff_u128 << (11 * 8));
                self.neon[0] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v0b12 => {
                self.neon[0] &= !(0xff_u128 << (12 * 8));
                self.neon[0] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v0b13 => {
                self.neon[0] &= !(0xff_u128 << (13 * 8));
                self.neon[0] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v0b14 => {
                self.neon[0] &= !(0xff_u128 << (14 * 8));
                self.neon[0] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v0b15 => {
                self.neon[0] &= !(0xff_u128 << (15 * 8));
                self.neon[0] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v1b0 => {
                self.neon[1] &= !(0xff_u128 << (0 * 8));
                self.neon[1] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v1b1 => {
                self.neon[1] &= !(0xff_u128 << (1 * 8));
                self.neon[1] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v1b2 => {
                self.neon[1] &= !(0xff_u128 << (2 * 8));
                self.neon[1] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v1b3 => {
                self.neon[1] &= !(0xff_u128 << (3 * 8));
                self.neon[1] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v1b4 => {
                self.neon[1] &= !(0xff_u128 << (4 * 8));
                self.neon[1] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v1b5 => {
                self.neon[1] &= !(0xff_u128 << (5 * 8));
                self.neon[1] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v1b6 => {
                self.neon[1] &= !(0xff_u128 << (6 * 8));
                self.neon[1] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v1b7 => {
                self.neon[1] &= !(0xff_u128 << (7 * 8));
                self.neon[1] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v1b8 => {
                self.neon[1] &= !(0xff_u128 << (8 * 8));
                self.neon[1] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v1b9 => {
                self.neon[1] &= !(0xff_u128 << (9 * 8));
                self.neon[1] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v1b10 => {
                self.neon[1] &= !(0xff_u128 << (10 * 8));
                self.neon[1] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v1b11 => {
                self.neon[1] &= !(0xff_u128 << (11 * 8));
                self.neon[1] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v1b12 => {
                self.neon[1] &= !(0xff_u128 << (12 * 8));
                self.neon[1] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v1b13 => {
                self.neon[1] &= !(0xff_u128 << (13 * 8));
                self.neon[1] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v1b14 => {
                self.neon[1] &= !(0xff_u128 << (14 * 8));
                self.neon[1] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v1b15 => {
                self.neon[1] &= !(0xff_u128 << (15 * 8));
                self.neon[1] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v2b0 => {
                self.neon[2] &= !(0xff_u128 << (0 * 8));
                self.neon[2] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v2b1 => {
                self.neon[2] &= !(0xff_u128 << (1 * 8));
                self.neon[2] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v2b2 => {
                self.neon[2] &= !(0xff_u128 << (2 * 8));
                self.neon[2] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v2b3 => {
                self.neon[2] &= !(0xff_u128 << (3 * 8));
                self.neon[2] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v2b4 => {
                self.neon[2] &= !(0xff_u128 << (4 * 8));
                self.neon[2] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v2b5 => {
                self.neon[2] &= !(0xff_u128 << (5 * 8));
                self.neon[2] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v2b6 => {
                self.neon[2] &= !(0xff_u128 << (6 * 8));
                self.neon[2] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v2b7 => {
                self.neon[2] &= !(0xff_u128 << (7 * 8));
                self.neon[2] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v2b8 => {
                self.neon[2] &= !(0xff_u128 << (8 * 8));
                self.neon[2] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v2b9 => {
                self.neon[2] &= !(0xff_u128 << (9 * 8));
                self.neon[2] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v2b10 => {
                self.neon[2] &= !(0xff_u128 << (10 * 8));
                self.neon[2] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v2b11 => {
                self.neon[2] &= !(0xff_u128 << (11 * 8));
                self.neon[2] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v2b12 => {
                self.neon[2] &= !(0xff_u128 << (12 * 8));
                self.neon[2] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v2b13 => {
                self.neon[2] &= !(0xff_u128 << (13 * 8));
                self.neon[2] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v2b14 => {
                self.neon[2] &= !(0xff_u128 << (14 * 8));
                self.neon[2] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v2b15 => {
                self.neon[2] &= !(0xff_u128 << (15 * 8));
                self.neon[2] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v3b0 => {
                self.neon[3] &= !(0xff_u128 << (0 * 8));
                self.neon[3] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v3b1 => {
                self.neon[3] &= !(0xff_u128 << (1 * 8));
                self.neon[3] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v3b2 => {
                self.neon[3] &= !(0xff_u128 << (2 * 8));
                self.neon[3] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v3b3 => {
                self.neon[3] &= !(0xff_u128 << (3 * 8));
                self.neon[3] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v3b4 => {
                self.neon[3] &= !(0xff_u128 << (4 * 8));
                self.neon[3] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v3b5 => {
                self.neon[3] &= !(0xff_u128 << (5 * 8));
                self.neon[3] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v3b6 => {
                self.neon[3] &= !(0xff_u128 << (6 * 8));
                self.neon[3] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v3b7 => {
                self.neon[3] &= !(0xff_u128 << (7 * 8));
                self.neon[3] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v3b8 => {
                self.neon[3] &= !(0xff_u128 << (8 * 8));
                self.neon[3] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v3b9 => {
                self.neon[3] &= !(0xff_u128 << (9 * 8));
                self.neon[3] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v3b10 => {
                self.neon[3] &= !(0xff_u128 << (10 * 8));
                self.neon[3] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v3b11 => {
                self.neon[3] &= !(0xff_u128 << (11 * 8));
                self.neon[3] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v3b12 => {
                self.neon[3] &= !(0xff_u128 << (12 * 8));
                self.neon[3] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v3b13 => {
                self.neon[3] &= !(0xff_u128 << (13 * 8));
                self.neon[3] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v3b14 => {
                self.neon[3] &= !(0xff_u128 << (14 * 8));
                self.neon[3] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v3b15 => {
                self.neon[3] &= !(0xff_u128 << (15 * 8));
                self.neon[3] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v4b0 => {
                self.neon[4] &= !(0xff_u128 << (0 * 8));
                self.neon[4] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v4b1 => {
                self.neon[4] &= !(0xff_u128 << (1 * 8));
                self.neon[4] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v4b2 => {
                self.neon[4] &= !(0xff_u128 << (2 * 8));
                self.neon[4] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v4b3 => {
                self.neon[4] &= !(0xff_u128 << (3 * 8));
                self.neon[4] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v4b4 => {
                self.neon[4] &= !(0xff_u128 << (4 * 8));
                self.neon[4] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v4b5 => {
                self.neon[4] &= !(0xff_u128 << (5 * 8));
                self.neon[4] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v4b6 => {
                self.neon[4] &= !(0xff_u128 << (6 * 8));
                self.neon[4] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v4b7 => {
                self.neon[4] &= !(0xff_u128 << (7 * 8));
                self.neon[4] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v4b8 => {
                self.neon[4] &= !(0xff_u128 << (8 * 8));
                self.neon[4] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v4b9 => {
                self.neon[4] &= !(0xff_u128 << (9 * 8));
                self.neon[4] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v4b10 => {
                self.neon[4] &= !(0xff_u128 << (10 * 8));
                self.neon[4] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v4b11 => {
                self.neon[4] &= !(0xff_u128 << (11 * 8));
                self.neon[4] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v4b12 => {
                self.neon[4] &= !(0xff_u128 << (12 * 8));
                self.neon[4] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v4b13 => {
                self.neon[4] &= !(0xff_u128 << (13 * 8));
                self.neon[4] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v4b14 => {
                self.neon[4] &= !(0xff_u128 << (14 * 8));
                self.neon[4] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v4b15 => {
                self.neon[4] &= !(0xff_u128 << (15 * 8));
                self.neon[4] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v5b0 => {
                self.neon[5] &= !(0xff_u128 << (0 * 8));
                self.neon[5] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v5b1 => {
                self.neon[5] &= !(0xff_u128 << (1 * 8));
                self.neon[5] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v5b2 => {
                self.neon[5] &= !(0xff_u128 << (2 * 8));
                self.neon[5] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v5b3 => {
                self.neon[5] &= !(0xff_u128 << (3 * 8));
                self.neon[5] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v5b4 => {
                self.neon[5] &= !(0xff_u128 << (4 * 8));
                self.neon[5] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v5b5 => {
                self.neon[5] &= !(0xff_u128 << (5 * 8));
                self.neon[5] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v5b6 => {
                self.neon[5] &= !(0xff_u128 << (6 * 8));
                self.neon[5] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v5b7 => {
                self.neon[5] &= !(0xff_u128 << (7 * 8));
                self.neon[5] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v5b8 => {
                self.neon[5] &= !(0xff_u128 << (8 * 8));
                self.neon[5] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v5b9 => {
                self.neon[5] &= !(0xff_u128 << (9 * 8));
                self.neon[5] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v5b10 => {
                self.neon[5] &= !(0xff_u128 << (10 * 8));
                self.neon[5] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v5b11 => {
                self.neon[5] &= !(0xff_u128 << (11 * 8));
                self.neon[5] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v5b12 => {
                self.neon[5] &= !(0xff_u128 << (12 * 8));
                self.neon[5] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v5b13 => {
                self.neon[5] &= !(0xff_u128 << (13 * 8));
                self.neon[5] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v5b14 => {
                self.neon[5] &= !(0xff_u128 << (14 * 8));
                self.neon[5] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v5b15 => {
                self.neon[5] &= !(0xff_u128 << (15 * 8));
                self.neon[5] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v6b0 => {
                self.neon[6] &= !(0xff_u128 << (0 * 8));
                self.neon[6] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v6b1 => {
                self.neon[6] &= !(0xff_u128 << (1 * 8));
                self.neon[6] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v6b2 => {
                self.neon[6] &= !(0xff_u128 << (2 * 8));
                self.neon[6] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v6b3 => {
                self.neon[6] &= !(0xff_u128 << (3 * 8));
                self.neon[6] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v6b4 => {
                self.neon[6] &= !(0xff_u128 << (4 * 8));
                self.neon[6] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v6b5 => {
                self.neon[6] &= !(0xff_u128 << (5 * 8));
                self.neon[6] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v6b6 => {
                self.neon[6] &= !(0xff_u128 << (6 * 8));
                self.neon[6] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v6b7 => {
                self.neon[6] &= !(0xff_u128 << (7 * 8));
                self.neon[6] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v6b8 => {
                self.neon[6] &= !(0xff_u128 << (8 * 8));
                self.neon[6] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v6b9 => {
                self.neon[6] &= !(0xff_u128 << (9 * 8));
                self.neon[6] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v6b10 => {
                self.neon[6] &= !(0xff_u128 << (10 * 8));
                self.neon[6] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v6b11 => {
                self.neon[6] &= !(0xff_u128 << (11 * 8));
                self.neon[6] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v6b12 => {
                self.neon[6] &= !(0xff_u128 << (12 * 8));
                self.neon[6] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v6b13 => {
                self.neon[6] &= !(0xff_u128 << (13 * 8));
                self.neon[6] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v6b14 => {
                self.neon[6] &= !(0xff_u128 << (14 * 8));
                self.neon[6] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v6b15 => {
                self.neon[6] &= !(0xff_u128 << (15 * 8));
                self.neon[6] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v7b0 => {
                self.neon[7] &= !(0xff_u128 << (0 * 8));
                self.neon[7] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v7b1 => {
                self.neon[7] &= !(0xff_u128 << (1 * 8));
                self.neon[7] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v7b2 => {
                self.neon[7] &= !(0xff_u128 << (2 * 8));
                self.neon[7] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v7b3 => {
                self.neon[7] &= !(0xff_u128 << (3 * 8));
                self.neon[7] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v7b4 => {
                self.neon[7] &= !(0xff_u128 << (4 * 8));
                self.neon[7] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v7b5 => {
                self.neon[7] &= !(0xff_u128 << (5 * 8));
                self.neon[7] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v7b6 => {
                self.neon[7] &= !(0xff_u128 << (6 * 8));
                self.neon[7] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v7b7 => {
                self.neon[7] &= !(0xff_u128 << (7 * 8));
                self.neon[7] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v7b8 => {
                self.neon[7] &= !(0xff_u128 << (8 * 8));
                self.neon[7] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v7b9 => {
                self.neon[7] &= !(0xff_u128 << (9 * 8));
                self.neon[7] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v7b10 => {
                self.neon[7] &= !(0xff_u128 << (10 * 8));
                self.neon[7] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v7b11 => {
                self.neon[7] &= !(0xff_u128 << (11 * 8));
                self.neon[7] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v7b12 => {
                self.neon[7] &= !(0xff_u128 << (12 * 8));
                self.neon[7] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v7b13 => {
                self.neon[7] &= !(0xff_u128 << (13 * 8));
                self.neon[7] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v7b14 => {
                self.neon[7] &= !(0xff_u128 << (14 * 8));
                self.neon[7] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v7b15 => {
                self.neon[7] &= !(0xff_u128 << (15 * 8));
                self.neon[7] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v8b0 => {
                self.neon[8] &= !(0xff_u128 << (0 * 8));
                self.neon[8] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v8b1 => {
                self.neon[8] &= !(0xff_u128 << (1 * 8));
                self.neon[8] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v8b2 => {
                self.neon[8] &= !(0xff_u128 << (2 * 8));
                self.neon[8] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v8b3 => {
                self.neon[8] &= !(0xff_u128 << (3 * 8));
                self.neon[8] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v8b4 => {
                self.neon[8] &= !(0xff_u128 << (4 * 8));
                self.neon[8] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v8b5 => {
                self.neon[8] &= !(0xff_u128 << (5 * 8));
                self.neon[8] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v8b6 => {
                self.neon[8] &= !(0xff_u128 << (6 * 8));
                self.neon[8] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v8b7 => {
                self.neon[8] &= !(0xff_u128 << (7 * 8));
                self.neon[8] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v8b8 => {
                self.neon[8] &= !(0xff_u128 << (8 * 8));
                self.neon[8] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v8b9 => {
                self.neon[8] &= !(0xff_u128 << (9 * 8));
                self.neon[8] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v8b10 => {
                self.neon[8] &= !(0xff_u128 << (10 * 8));
                self.neon[8] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v8b11 => {
                self.neon[8] &= !(0xff_u128 << (11 * 8));
                self.neon[8] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v8b12 => {
                self.neon[8] &= !(0xff_u128 << (12 * 8));
                self.neon[8] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v8b13 => {
                self.neon[8] &= !(0xff_u128 << (13 * 8));
                self.neon[8] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v8b14 => {
                self.neon[8] &= !(0xff_u128 << (14 * 8));
                self.neon[8] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v8b15 => {
                self.neon[8] &= !(0xff_u128 << (15 * 8));
                self.neon[8] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v9b0 => {
                self.neon[9] &= !(0xff_u128 << (0 * 8));
                self.neon[9] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v9b1 => {
                self.neon[9] &= !(0xff_u128 << (1 * 8));
                self.neon[9] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v9b2 => {
                self.neon[9] &= !(0xff_u128 << (2 * 8));
                self.neon[9] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v9b3 => {
                self.neon[9] &= !(0xff_u128 << (3 * 8));
                self.neon[9] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v9b4 => {
                self.neon[9] &= !(0xff_u128 << (4 * 8));
                self.neon[9] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v9b5 => {
                self.neon[9] &= !(0xff_u128 << (5 * 8));
                self.neon[9] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v9b6 => {
                self.neon[9] &= !(0xff_u128 << (6 * 8));
                self.neon[9] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v9b7 => {
                self.neon[9] &= !(0xff_u128 << (7 * 8));
                self.neon[9] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v9b8 => {
                self.neon[9] &= !(0xff_u128 << (8 * 8));
                self.neon[9] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v9b9 => {
                self.neon[9] &= !(0xff_u128 << (9 * 8));
                self.neon[9] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v9b10 => {
                self.neon[9] &= !(0xff_u128 << (10 * 8));
                self.neon[9] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v9b11 => {
                self.neon[9] &= !(0xff_u128 << (11 * 8));
                self.neon[9] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v9b12 => {
                self.neon[9] &= !(0xff_u128 << (12 * 8));
                self.neon[9] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v9b13 => {
                self.neon[9] &= !(0xff_u128 << (13 * 8));
                self.neon[9] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v9b14 => {
                self.neon[9] &= !(0xff_u128 << (14 * 8));
                self.neon[9] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v9b15 => {
                self.neon[9] &= !(0xff_u128 << (15 * 8));
                self.neon[9] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v10b0 => {
                self.neon[10] &= !(0xff_u128 << (0 * 8));
                self.neon[10] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v10b1 => {
                self.neon[10] &= !(0xff_u128 << (1 * 8));
                self.neon[10] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v10b2 => {
                self.neon[10] &= !(0xff_u128 << (2 * 8));
                self.neon[10] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v10b3 => {
                self.neon[10] &= !(0xff_u128 << (3 * 8));
                self.neon[10] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v10b4 => {
                self.neon[10] &= !(0xff_u128 << (4 * 8));
                self.neon[10] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v10b5 => {
                self.neon[10] &= !(0xff_u128 << (5 * 8));
                self.neon[10] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v10b6 => {
                self.neon[10] &= !(0xff_u128 << (6 * 8));
                self.neon[10] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v10b7 => {
                self.neon[10] &= !(0xff_u128 << (7 * 8));
                self.neon[10] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v10b8 => {
                self.neon[10] &= !(0xff_u128 << (8 * 8));
                self.neon[10] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v10b9 => {
                self.neon[10] &= !(0xff_u128 << (9 * 8));
                self.neon[10] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v10b10 => {
                self.neon[10] &= !(0xff_u128 << (10 * 8));
                self.neon[10] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v10b11 => {
                self.neon[10] &= !(0xff_u128 << (11 * 8));
                self.neon[10] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v10b12 => {
                self.neon[10] &= !(0xff_u128 << (12 * 8));
                self.neon[10] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v10b13 => {
                self.neon[10] &= !(0xff_u128 << (13 * 8));
                self.neon[10] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v10b14 => {
                self.neon[10] &= !(0xff_u128 << (14 * 8));
                self.neon[10] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v10b15 => {
                self.neon[10] &= !(0xff_u128 << (15 * 8));
                self.neon[10] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v11b0 => {
                self.neon[11] &= !(0xff_u128 << (0 * 8));
                self.neon[11] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v11b1 => {
                self.neon[11] &= !(0xff_u128 << (1 * 8));
                self.neon[11] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v11b2 => {
                self.neon[11] &= !(0xff_u128 << (2 * 8));
                self.neon[11] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v11b3 => {
                self.neon[11] &= !(0xff_u128 << (3 * 8));
                self.neon[11] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v11b4 => {
                self.neon[11] &= !(0xff_u128 << (4 * 8));
                self.neon[11] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v11b5 => {
                self.neon[11] &= !(0xff_u128 << (5 * 8));
                self.neon[11] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v11b6 => {
                self.neon[11] &= !(0xff_u128 << (6 * 8));
                self.neon[11] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v11b7 => {
                self.neon[11] &= !(0xff_u128 << (7 * 8));
                self.neon[11] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v11b8 => {
                self.neon[11] &= !(0xff_u128 << (8 * 8));
                self.neon[11] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v11b9 => {
                self.neon[11] &= !(0xff_u128 << (9 * 8));
                self.neon[11] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v11b10 => {
                self.neon[11] &= !(0xff_u128 << (10 * 8));
                self.neon[11] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v11b11 => {
                self.neon[11] &= !(0xff_u128 << (11 * 8));
                self.neon[11] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v11b12 => {
                self.neon[11] &= !(0xff_u128 << (12 * 8));
                self.neon[11] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v11b13 => {
                self.neon[11] &= !(0xff_u128 << (13 * 8));
                self.neon[11] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v11b14 => {
                self.neon[11] &= !(0xff_u128 << (14 * 8));
                self.neon[11] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v11b15 => {
                self.neon[11] &= !(0xff_u128 << (15 * 8));
                self.neon[11] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v12b0 => {
                self.neon[12] &= !(0xff_u128 << (0 * 8));
                self.neon[12] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v12b1 => {
                self.neon[12] &= !(0xff_u128 << (1 * 8));
                self.neon[12] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v12b2 => {
                self.neon[12] &= !(0xff_u128 << (2 * 8));
                self.neon[12] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v12b3 => {
                self.neon[12] &= !(0xff_u128 << (3 * 8));
                self.neon[12] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v12b4 => {
                self.neon[12] &= !(0xff_u128 << (4 * 8));
                self.neon[12] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v12b5 => {
                self.neon[12] &= !(0xff_u128 << (5 * 8));
                self.neon[12] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v12b6 => {
                self.neon[12] &= !(0xff_u128 << (6 * 8));
                self.neon[12] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v12b7 => {
                self.neon[12] &= !(0xff_u128 << (7 * 8));
                self.neon[12] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v12b8 => {
                self.neon[12] &= !(0xff_u128 << (8 * 8));
                self.neon[12] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v12b9 => {
                self.neon[12] &= !(0xff_u128 << (9 * 8));
                self.neon[12] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v12b10 => {
                self.neon[12] &= !(0xff_u128 << (10 * 8));
                self.neon[12] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v12b11 => {
                self.neon[12] &= !(0xff_u128 << (11 * 8));
                self.neon[12] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v12b12 => {
                self.neon[12] &= !(0xff_u128 << (12 * 8));
                self.neon[12] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v12b13 => {
                self.neon[12] &= !(0xff_u128 << (13 * 8));
                self.neon[12] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v12b14 => {
                self.neon[12] &= !(0xff_u128 << (14 * 8));
                self.neon[12] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v12b15 => {
                self.neon[12] &= !(0xff_u128 << (15 * 8));
                self.neon[12] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v13b0 => {
                self.neon[13] &= !(0xff_u128 << (0 * 8));
                self.neon[13] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v13b1 => {
                self.neon[13] &= !(0xff_u128 << (1 * 8));
                self.neon[13] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v13b2 => {
                self.neon[13] &= !(0xff_u128 << (2 * 8));
                self.neon[13] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v13b3 => {
                self.neon[13] &= !(0xff_u128 << (3 * 8));
                self.neon[13] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v13b4 => {
                self.neon[13] &= !(0xff_u128 << (4 * 8));
                self.neon[13] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v13b5 => {
                self.neon[13] &= !(0xff_u128 << (5 * 8));
                self.neon[13] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v13b6 => {
                self.neon[13] &= !(0xff_u128 << (6 * 8));
                self.neon[13] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v13b7 => {
                self.neon[13] &= !(0xff_u128 << (7 * 8));
                self.neon[13] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v13b8 => {
                self.neon[13] &= !(0xff_u128 << (8 * 8));
                self.neon[13] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v13b9 => {
                self.neon[13] &= !(0xff_u128 << (9 * 8));
                self.neon[13] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v13b10 => {
                self.neon[13] &= !(0xff_u128 << (10 * 8));
                self.neon[13] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v13b11 => {
                self.neon[13] &= !(0xff_u128 << (11 * 8));
                self.neon[13] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v13b12 => {
                self.neon[13] &= !(0xff_u128 << (12 * 8));
                self.neon[13] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v13b13 => {
                self.neon[13] &= !(0xff_u128 << (13 * 8));
                self.neon[13] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v13b14 => {
                self.neon[13] &= !(0xff_u128 << (14 * 8));
                self.neon[13] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v13b15 => {
                self.neon[13] &= !(0xff_u128 << (15 * 8));
                self.neon[13] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v14b0 => {
                self.neon[14] &= !(0xff_u128 << (0 * 8));
                self.neon[14] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v14b1 => {
                self.neon[14] &= !(0xff_u128 << (1 * 8));
                self.neon[14] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v14b2 => {
                self.neon[14] &= !(0xff_u128 << (2 * 8));
                self.neon[14] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v14b3 => {
                self.neon[14] &= !(0xff_u128 << (3 * 8));
                self.neon[14] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v14b4 => {
                self.neon[14] &= !(0xff_u128 << (4 * 8));
                self.neon[14] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v14b5 => {
                self.neon[14] &= !(0xff_u128 << (5 * 8));
                self.neon[14] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v14b6 => {
                self.neon[14] &= !(0xff_u128 << (6 * 8));
                self.neon[14] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v14b7 => {
                self.neon[14] &= !(0xff_u128 << (7 * 8));
                self.neon[14] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v14b8 => {
                self.neon[14] &= !(0xff_u128 << (8 * 8));
                self.neon[14] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v14b9 => {
                self.neon[14] &= !(0xff_u128 << (9 * 8));
                self.neon[14] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v14b10 => {
                self.neon[14] &= !(0xff_u128 << (10 * 8));
                self.neon[14] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v14b11 => {
                self.neon[14] &= !(0xff_u128 << (11 * 8));
                self.neon[14] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v14b12 => {
                self.neon[14] &= !(0xff_u128 << (12 * 8));
                self.neon[14] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v14b13 => {
                self.neon[14] &= !(0xff_u128 << (13 * 8));
                self.neon[14] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v14b14 => {
                self.neon[14] &= !(0xff_u128 << (14 * 8));
                self.neon[14] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v14b15 => {
                self.neon[14] &= !(0xff_u128 << (15 * 8));
                self.neon[14] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v15b0 => {
                self.neon[15] &= !(0xff_u128 << (0 * 8));
                self.neon[15] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v15b1 => {
                self.neon[15] &= !(0xff_u128 << (1 * 8));
                self.neon[15] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v15b2 => {
                self.neon[15] &= !(0xff_u128 << (2 * 8));
                self.neon[15] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v15b3 => {
                self.neon[15] &= !(0xff_u128 << (3 * 8));
                self.neon[15] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v15b4 => {
                self.neon[15] &= !(0xff_u128 << (4 * 8));
                self.neon[15] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v15b5 => {
                self.neon[15] &= !(0xff_u128 << (5 * 8));
                self.neon[15] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v15b6 => {
                self.neon[15] &= !(0xff_u128 << (6 * 8));
                self.neon[15] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v15b7 => {
                self.neon[15] &= !(0xff_u128 << (7 * 8));
                self.neon[15] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v15b8 => {
                self.neon[15] &= !(0xff_u128 << (8 * 8));
                self.neon[15] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v15b9 => {
                self.neon[15] &= !(0xff_u128 << (9 * 8));
                self.neon[15] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v15b10 => {
                self.neon[15] &= !(0xff_u128 << (10 * 8));
                self.neon[15] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v15b11 => {
                self.neon[15] &= !(0xff_u128 << (11 * 8));
                self.neon[15] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v15b12 => {
                self.neon[15] &= !(0xff_u128 << (12 * 8));
                self.neon[15] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v15b13 => {
                self.neon[15] &= !(0xff_u128 << (13 * 8));
                self.neon[15] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v15b14 => {
                self.neon[15] &= !(0xff_u128 << (14 * 8));
                self.neon[15] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v15b15 => {
                self.neon[15] &= !(0xff_u128 << (15 * 8));
                self.neon[15] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v16b0 => {
                self.neon[16] &= !(0xff_u128 << (0 * 8));
                self.neon[16] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v16b1 => {
                self.neon[16] &= !(0xff_u128 << (1 * 8));
                self.neon[16] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v16b2 => {
                self.neon[16] &= !(0xff_u128 << (2 * 8));
                self.neon[16] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v16b3 => {
                self.neon[16] &= !(0xff_u128 << (3 * 8));
                self.neon[16] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v16b4 => {
                self.neon[16] &= !(0xff_u128 << (4 * 8));
                self.neon[16] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v16b5 => {
                self.neon[16] &= !(0xff_u128 << (5 * 8));
                self.neon[16] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v16b6 => {
                self.neon[16] &= !(0xff_u128 << (6 * 8));
                self.neon[16] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v16b7 => {
                self.neon[16] &= !(0xff_u128 << (7 * 8));
                self.neon[16] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v16b8 => {
                self.neon[16] &= !(0xff_u128 << (8 * 8));
                self.neon[16] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v16b9 => {
                self.neon[16] &= !(0xff_u128 << (9 * 8));
                self.neon[16] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v16b10 => {
                self.neon[16] &= !(0xff_u128 << (10 * 8));
                self.neon[16] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v16b11 => {
                self.neon[16] &= !(0xff_u128 << (11 * 8));
                self.neon[16] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v16b12 => {
                self.neon[16] &= !(0xff_u128 << (12 * 8));
                self.neon[16] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v16b13 => {
                self.neon[16] &= !(0xff_u128 << (13 * 8));
                self.neon[16] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v16b14 => {
                self.neon[16] &= !(0xff_u128 << (14 * 8));
                self.neon[16] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v16b15 => {
                self.neon[16] &= !(0xff_u128 << (15 * 8));
                self.neon[16] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v17b0 => {
                self.neon[17] &= !(0xff_u128 << (0 * 8));
                self.neon[17] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v17b1 => {
                self.neon[17] &= !(0xff_u128 << (1 * 8));
                self.neon[17] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v17b2 => {
                self.neon[17] &= !(0xff_u128 << (2 * 8));
                self.neon[17] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v17b3 => {
                self.neon[17] &= !(0xff_u128 << (3 * 8));
                self.neon[17] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v17b4 => {
                self.neon[17] &= !(0xff_u128 << (4 * 8));
                self.neon[17] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v17b5 => {
                self.neon[17] &= !(0xff_u128 << (5 * 8));
                self.neon[17] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v17b6 => {
                self.neon[17] &= !(0xff_u128 << (6 * 8));
                self.neon[17] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v17b7 => {
                self.neon[17] &= !(0xff_u128 << (7 * 8));
                self.neon[17] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v17b8 => {
                self.neon[17] &= !(0xff_u128 << (8 * 8));
                self.neon[17] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v17b9 => {
                self.neon[17] &= !(0xff_u128 << (9 * 8));
                self.neon[17] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v17b10 => {
                self.neon[17] &= !(0xff_u128 << (10 * 8));
                self.neon[17] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v17b11 => {
                self.neon[17] &= !(0xff_u128 << (11 * 8));
                self.neon[17] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v17b12 => {
                self.neon[17] &= !(0xff_u128 << (12 * 8));
                self.neon[17] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v17b13 => {
                self.neon[17] &= !(0xff_u128 << (13 * 8));
                self.neon[17] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v17b14 => {
                self.neon[17] &= !(0xff_u128 << (14 * 8));
                self.neon[17] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v17b15 => {
                self.neon[17] &= !(0xff_u128 << (15 * 8));
                self.neon[17] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v18b0 => {
                self.neon[18] &= !(0xff_u128 << (0 * 8));
                self.neon[18] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v18b1 => {
                self.neon[18] &= !(0xff_u128 << (1 * 8));
                self.neon[18] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v18b2 => {
                self.neon[18] &= !(0xff_u128 << (2 * 8));
                self.neon[18] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v18b3 => {
                self.neon[18] &= !(0xff_u128 << (3 * 8));
                self.neon[18] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v18b4 => {
                self.neon[18] &= !(0xff_u128 << (4 * 8));
                self.neon[18] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v18b5 => {
                self.neon[18] &= !(0xff_u128 << (5 * 8));
                self.neon[18] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v18b6 => {
                self.neon[18] &= !(0xff_u128 << (6 * 8));
                self.neon[18] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v18b7 => {
                self.neon[18] &= !(0xff_u128 << (7 * 8));
                self.neon[18] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v18b8 => {
                self.neon[18] &= !(0xff_u128 << (8 * 8));
                self.neon[18] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v18b9 => {
                self.neon[18] &= !(0xff_u128 << (9 * 8));
                self.neon[18] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v18b10 => {
                self.neon[18] &= !(0xff_u128 << (10 * 8));
                self.neon[18] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v18b11 => {
                self.neon[18] &= !(0xff_u128 << (11 * 8));
                self.neon[18] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v18b12 => {
                self.neon[18] &= !(0xff_u128 << (12 * 8));
                self.neon[18] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v18b13 => {
                self.neon[18] &= !(0xff_u128 << (13 * 8));
                self.neon[18] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v18b14 => {
                self.neon[18] &= !(0xff_u128 << (14 * 8));
                self.neon[18] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v18b15 => {
                self.neon[18] &= !(0xff_u128 << (15 * 8));
                self.neon[18] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v19b0 => {
                self.neon[19] &= !(0xff_u128 << (0 * 8));
                self.neon[19] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v19b1 => {
                self.neon[19] &= !(0xff_u128 << (1 * 8));
                self.neon[19] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v19b2 => {
                self.neon[19] &= !(0xff_u128 << (2 * 8));
                self.neon[19] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v19b3 => {
                self.neon[19] &= !(0xff_u128 << (3 * 8));
                self.neon[19] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v19b4 => {
                self.neon[19] &= !(0xff_u128 << (4 * 8));
                self.neon[19] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v19b5 => {
                self.neon[19] &= !(0xff_u128 << (5 * 8));
                self.neon[19] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v19b6 => {
                self.neon[19] &= !(0xff_u128 << (6 * 8));
                self.neon[19] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v19b7 => {
                self.neon[19] &= !(0xff_u128 << (7 * 8));
                self.neon[19] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v19b8 => {
                self.neon[19] &= !(0xff_u128 << (8 * 8));
                self.neon[19] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v19b9 => {
                self.neon[19] &= !(0xff_u128 << (9 * 8));
                self.neon[19] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v19b10 => {
                self.neon[19] &= !(0xff_u128 << (10 * 8));
                self.neon[19] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v19b11 => {
                self.neon[19] &= !(0xff_u128 << (11 * 8));
                self.neon[19] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v19b12 => {
                self.neon[19] &= !(0xff_u128 << (12 * 8));
                self.neon[19] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v19b13 => {
                self.neon[19] &= !(0xff_u128 << (13 * 8));
                self.neon[19] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v19b14 => {
                self.neon[19] &= !(0xff_u128 << (14 * 8));
                self.neon[19] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v19b15 => {
                self.neon[19] &= !(0xff_u128 << (15 * 8));
                self.neon[19] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v20b0 => {
                self.neon[20] &= !(0xff_u128 << (0 * 8));
                self.neon[20] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v20b1 => {
                self.neon[20] &= !(0xff_u128 << (1 * 8));
                self.neon[20] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v20b2 => {
                self.neon[20] &= !(0xff_u128 << (2 * 8));
                self.neon[20] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v20b3 => {
                self.neon[20] &= !(0xff_u128 << (3 * 8));
                self.neon[20] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v20b4 => {
                self.neon[20] &= !(0xff_u128 << (4 * 8));
                self.neon[20] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v20b5 => {
                self.neon[20] &= !(0xff_u128 << (5 * 8));
                self.neon[20] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v20b6 => {
                self.neon[20] &= !(0xff_u128 << (6 * 8));
                self.neon[20] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v20b7 => {
                self.neon[20] &= !(0xff_u128 << (7 * 8));
                self.neon[20] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v20b8 => {
                self.neon[20] &= !(0xff_u128 << (8 * 8));
                self.neon[20] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v20b9 => {
                self.neon[20] &= !(0xff_u128 << (9 * 8));
                self.neon[20] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v20b10 => {
                self.neon[20] &= !(0xff_u128 << (10 * 8));
                self.neon[20] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v20b11 => {
                self.neon[20] &= !(0xff_u128 << (11 * 8));
                self.neon[20] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v20b12 => {
                self.neon[20] &= !(0xff_u128 << (12 * 8));
                self.neon[20] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v20b13 => {
                self.neon[20] &= !(0xff_u128 << (13 * 8));
                self.neon[20] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v20b14 => {
                self.neon[20] &= !(0xff_u128 << (14 * 8));
                self.neon[20] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v20b15 => {
                self.neon[20] &= !(0xff_u128 << (15 * 8));
                self.neon[20] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v21b0 => {
                self.neon[21] &= !(0xff_u128 << (0 * 8));
                self.neon[21] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v21b1 => {
                self.neon[21] &= !(0xff_u128 << (1 * 8));
                self.neon[21] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v21b2 => {
                self.neon[21] &= !(0xff_u128 << (2 * 8));
                self.neon[21] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v21b3 => {
                self.neon[21] &= !(0xff_u128 << (3 * 8));
                self.neon[21] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v21b4 => {
                self.neon[21] &= !(0xff_u128 << (4 * 8));
                self.neon[21] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v21b5 => {
                self.neon[21] &= !(0xff_u128 << (5 * 8));
                self.neon[21] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v21b6 => {
                self.neon[21] &= !(0xff_u128 << (6 * 8));
                self.neon[21] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v21b7 => {
                self.neon[21] &= !(0xff_u128 << (7 * 8));
                self.neon[21] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v21b8 => {
                self.neon[21] &= !(0xff_u128 << (8 * 8));
                self.neon[21] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v21b9 => {
                self.neon[21] &= !(0xff_u128 << (9 * 8));
                self.neon[21] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v21b10 => {
                self.neon[21] &= !(0xff_u128 << (10 * 8));
                self.neon[21] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v21b11 => {
                self.neon[21] &= !(0xff_u128 << (11 * 8));
                self.neon[21] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v21b12 => {
                self.neon[21] &= !(0xff_u128 << (12 * 8));
                self.neon[21] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v21b13 => {
                self.neon[21] &= !(0xff_u128 << (13 * 8));
                self.neon[21] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v21b14 => {
                self.neon[21] &= !(0xff_u128 << (14 * 8));
                self.neon[21] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v21b15 => {
                self.neon[21] &= !(0xff_u128 << (15 * 8));
                self.neon[21] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v22b0 => {
                self.neon[22] &= !(0xff_u128 << (0 * 8));
                self.neon[22] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v22b1 => {
                self.neon[22] &= !(0xff_u128 << (1 * 8));
                self.neon[22] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v22b2 => {
                self.neon[22] &= !(0xff_u128 << (2 * 8));
                self.neon[22] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v22b3 => {
                self.neon[22] &= !(0xff_u128 << (3 * 8));
                self.neon[22] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v22b4 => {
                self.neon[22] &= !(0xff_u128 << (4 * 8));
                self.neon[22] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v22b5 => {
                self.neon[22] &= !(0xff_u128 << (5 * 8));
                self.neon[22] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v22b6 => {
                self.neon[22] &= !(0xff_u128 << (6 * 8));
                self.neon[22] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v22b7 => {
                self.neon[22] &= !(0xff_u128 << (7 * 8));
                self.neon[22] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v22b8 => {
                self.neon[22] &= !(0xff_u128 << (8 * 8));
                self.neon[22] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v22b9 => {
                self.neon[22] &= !(0xff_u128 << (9 * 8));
                self.neon[22] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v22b10 => {
                self.neon[22] &= !(0xff_u128 << (10 * 8));
                self.neon[22] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v22b11 => {
                self.neon[22] &= !(0xff_u128 << (11 * 8));
                self.neon[22] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v22b12 => {
                self.neon[22] &= !(0xff_u128 << (12 * 8));
                self.neon[22] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v22b13 => {
                self.neon[22] &= !(0xff_u128 << (13 * 8));
                self.neon[22] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v22b14 => {
                self.neon[22] &= !(0xff_u128 << (14 * 8));
                self.neon[22] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v22b15 => {
                self.neon[22] &= !(0xff_u128 << (15 * 8));
                self.neon[22] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v23b0 => {
                self.neon[23] &= !(0xff_u128 << (0 * 8));
                self.neon[23] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v23b1 => {
                self.neon[23] &= !(0xff_u128 << (1 * 8));
                self.neon[23] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v23b2 => {
                self.neon[23] &= !(0xff_u128 << (2 * 8));
                self.neon[23] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v23b3 => {
                self.neon[23] &= !(0xff_u128 << (3 * 8));
                self.neon[23] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v23b4 => {
                self.neon[23] &= !(0xff_u128 << (4 * 8));
                self.neon[23] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v23b5 => {
                self.neon[23] &= !(0xff_u128 << (5 * 8));
                self.neon[23] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v23b6 => {
                self.neon[23] &= !(0xff_u128 << (6 * 8));
                self.neon[23] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v23b7 => {
                self.neon[23] &= !(0xff_u128 << (7 * 8));
                self.neon[23] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v23b8 => {
                self.neon[23] &= !(0xff_u128 << (8 * 8));
                self.neon[23] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v23b9 => {
                self.neon[23] &= !(0xff_u128 << (9 * 8));
                self.neon[23] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v23b10 => {
                self.neon[23] &= !(0xff_u128 << (10 * 8));
                self.neon[23] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v23b11 => {
                self.neon[23] &= !(0xff_u128 << (11 * 8));
                self.neon[23] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v23b12 => {
                self.neon[23] &= !(0xff_u128 << (12 * 8));
                self.neon[23] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v23b13 => {
                self.neon[23] &= !(0xff_u128 << (13 * 8));
                self.neon[23] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v23b14 => {
                self.neon[23] &= !(0xff_u128 << (14 * 8));
                self.neon[23] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v23b15 => {
                self.neon[23] &= !(0xff_u128 << (15 * 8));
                self.neon[23] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v24b0 => {
                self.neon[24] &= !(0xff_u128 << (0 * 8));
                self.neon[24] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v24b1 => {
                self.neon[24] &= !(0xff_u128 << (1 * 8));
                self.neon[24] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v24b2 => {
                self.neon[24] &= !(0xff_u128 << (2 * 8));
                self.neon[24] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v24b3 => {
                self.neon[24] &= !(0xff_u128 << (3 * 8));
                self.neon[24] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v24b4 => {
                self.neon[24] &= !(0xff_u128 << (4 * 8));
                self.neon[24] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v24b5 => {
                self.neon[24] &= !(0xff_u128 << (5 * 8));
                self.neon[24] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v24b6 => {
                self.neon[24] &= !(0xff_u128 << (6 * 8));
                self.neon[24] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v24b7 => {
                self.neon[24] &= !(0xff_u128 << (7 * 8));
                self.neon[24] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v24b8 => {
                self.neon[24] &= !(0xff_u128 << (8 * 8));
                self.neon[24] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v24b9 => {
                self.neon[24] &= !(0xff_u128 << (9 * 8));
                self.neon[24] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v24b10 => {
                self.neon[24] &= !(0xff_u128 << (10 * 8));
                self.neon[24] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v24b11 => {
                self.neon[24] &= !(0xff_u128 << (11 * 8));
                self.neon[24] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v24b12 => {
                self.neon[24] &= !(0xff_u128 << (12 * 8));
                self.neon[24] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v24b13 => {
                self.neon[24] &= !(0xff_u128 << (13 * 8));
                self.neon[24] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v24b14 => {
                self.neon[24] &= !(0xff_u128 << (14 * 8));
                self.neon[24] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v24b15 => {
                self.neon[24] &= !(0xff_u128 << (15 * 8));
                self.neon[24] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v25b0 => {
                self.neon[25] &= !(0xff_u128 << (0 * 8));
                self.neon[25] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v25b1 => {
                self.neon[25] &= !(0xff_u128 << (1 * 8));
                self.neon[25] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v25b2 => {
                self.neon[25] &= !(0xff_u128 << (2 * 8));
                self.neon[25] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v25b3 => {
                self.neon[25] &= !(0xff_u128 << (3 * 8));
                self.neon[25] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v25b4 => {
                self.neon[25] &= !(0xff_u128 << (4 * 8));
                self.neon[25] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v25b5 => {
                self.neon[25] &= !(0xff_u128 << (5 * 8));
                self.neon[25] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v25b6 => {
                self.neon[25] &= !(0xff_u128 << (6 * 8));
                self.neon[25] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v25b7 => {
                self.neon[25] &= !(0xff_u128 << (7 * 8));
                self.neon[25] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v25b8 => {
                self.neon[25] &= !(0xff_u128 << (8 * 8));
                self.neon[25] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v25b9 => {
                self.neon[25] &= !(0xff_u128 << (9 * 8));
                self.neon[25] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v25b10 => {
                self.neon[25] &= !(0xff_u128 << (10 * 8));
                self.neon[25] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v25b11 => {
                self.neon[25] &= !(0xff_u128 << (11 * 8));
                self.neon[25] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v25b12 => {
                self.neon[25] &= !(0xff_u128 << (12 * 8));
                self.neon[25] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v25b13 => {
                self.neon[25] &= !(0xff_u128 << (13 * 8));
                self.neon[25] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v25b14 => {
                self.neon[25] &= !(0xff_u128 << (14 * 8));
                self.neon[25] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v25b15 => {
                self.neon[25] &= !(0xff_u128 << (15 * 8));
                self.neon[25] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v26b0 => {
                self.neon[26] &= !(0xff_u128 << (0 * 8));
                self.neon[26] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v26b1 => {
                self.neon[26] &= !(0xff_u128 << (1 * 8));
                self.neon[26] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v26b2 => {
                self.neon[26] &= !(0xff_u128 << (2 * 8));
                self.neon[26] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v26b3 => {
                self.neon[26] &= !(0xff_u128 << (3 * 8));
                self.neon[26] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v26b4 => {
                self.neon[26] &= !(0xff_u128 << (4 * 8));
                self.neon[26] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v26b5 => {
                self.neon[26] &= !(0xff_u128 << (5 * 8));
                self.neon[26] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v26b6 => {
                self.neon[26] &= !(0xff_u128 << (6 * 8));
                self.neon[26] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v26b7 => {
                self.neon[26] &= !(0xff_u128 << (7 * 8));
                self.neon[26] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v26b8 => {
                self.neon[26] &= !(0xff_u128 << (8 * 8));
                self.neon[26] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v26b9 => {
                self.neon[26] &= !(0xff_u128 << (9 * 8));
                self.neon[26] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v26b10 => {
                self.neon[26] &= !(0xff_u128 << (10 * 8));
                self.neon[26] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v26b11 => {
                self.neon[26] &= !(0xff_u128 << (11 * 8));
                self.neon[26] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v26b12 => {
                self.neon[26] &= !(0xff_u128 << (12 * 8));
                self.neon[26] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v26b13 => {
                self.neon[26] &= !(0xff_u128 << (13 * 8));
                self.neon[26] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v26b14 => {
                self.neon[26] &= !(0xff_u128 << (14 * 8));
                self.neon[26] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v26b15 => {
                self.neon[26] &= !(0xff_u128 << (15 * 8));
                self.neon[26] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v27b0 => {
                self.neon[27] &= !(0xff_u128 << (0 * 8));
                self.neon[27] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v27b1 => {
                self.neon[27] &= !(0xff_u128 << (1 * 8));
                self.neon[27] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v27b2 => {
                self.neon[27] &= !(0xff_u128 << (2 * 8));
                self.neon[27] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v27b3 => {
                self.neon[27] &= !(0xff_u128 << (3 * 8));
                self.neon[27] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v27b4 => {
                self.neon[27] &= !(0xff_u128 << (4 * 8));
                self.neon[27] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v27b5 => {
                self.neon[27] &= !(0xff_u128 << (5 * 8));
                self.neon[27] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v27b6 => {
                self.neon[27] &= !(0xff_u128 << (6 * 8));
                self.neon[27] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v27b7 => {
                self.neon[27] &= !(0xff_u128 << (7 * 8));
                self.neon[27] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v27b8 => {
                self.neon[27] &= !(0xff_u128 << (8 * 8));
                self.neon[27] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v27b9 => {
                self.neon[27] &= !(0xff_u128 << (9 * 8));
                self.neon[27] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v27b10 => {
                self.neon[27] &= !(0xff_u128 << (10 * 8));
                self.neon[27] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v27b11 => {
                self.neon[27] &= !(0xff_u128 << (11 * 8));
                self.neon[27] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v27b12 => {
                self.neon[27] &= !(0xff_u128 << (12 * 8));
                self.neon[27] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v27b13 => {
                self.neon[27] &= !(0xff_u128 << (13 * 8));
                self.neon[27] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v27b14 => {
                self.neon[27] &= !(0xff_u128 << (14 * 8));
                self.neon[27] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v27b15 => {
                self.neon[27] &= !(0xff_u128 << (15 * 8));
                self.neon[27] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v28b0 => {
                self.neon[28] &= !(0xff_u128 << (0 * 8));
                self.neon[28] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v28b1 => {
                self.neon[28] &= !(0xff_u128 << (1 * 8));
                self.neon[28] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v28b2 => {
                self.neon[28] &= !(0xff_u128 << (2 * 8));
                self.neon[28] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v28b3 => {
                self.neon[28] &= !(0xff_u128 << (3 * 8));
                self.neon[28] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v28b4 => {
                self.neon[28] &= !(0xff_u128 << (4 * 8));
                self.neon[28] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v28b5 => {
                self.neon[28] &= !(0xff_u128 << (5 * 8));
                self.neon[28] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v28b6 => {
                self.neon[28] &= !(0xff_u128 << (6 * 8));
                self.neon[28] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v28b7 => {
                self.neon[28] &= !(0xff_u128 << (7 * 8));
                self.neon[28] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v28b8 => {
                self.neon[28] &= !(0xff_u128 << (8 * 8));
                self.neon[28] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v28b9 => {
                self.neon[28] &= !(0xff_u128 << (9 * 8));
                self.neon[28] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v28b10 => {
                self.neon[28] &= !(0xff_u128 << (10 * 8));
                self.neon[28] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v28b11 => {
                self.neon[28] &= !(0xff_u128 << (11 * 8));
                self.neon[28] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v28b12 => {
                self.neon[28] &= !(0xff_u128 << (12 * 8));
                self.neon[28] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v28b13 => {
                self.neon[28] &= !(0xff_u128 << (13 * 8));
                self.neon[28] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v28b14 => {
                self.neon[28] &= !(0xff_u128 << (14 * 8));
                self.neon[28] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v28b15 => {
                self.neon[28] &= !(0xff_u128 << (15 * 8));
                self.neon[28] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v29b0 => {
                self.neon[29] &= !(0xff_u128 << (0 * 8));
                self.neon[29] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v29b1 => {
                self.neon[29] &= !(0xff_u128 << (1 * 8));
                self.neon[29] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v29b2 => {
                self.neon[29] &= !(0xff_u128 << (2 * 8));
                self.neon[29] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v29b3 => {
                self.neon[29] &= !(0xff_u128 << (3 * 8));
                self.neon[29] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v29b4 => {
                self.neon[29] &= !(0xff_u128 << (4 * 8));
                self.neon[29] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v29b5 => {
                self.neon[29] &= !(0xff_u128 << (5 * 8));
                self.neon[29] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v29b6 => {
                self.neon[29] &= !(0xff_u128 << (6 * 8));
                self.neon[29] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v29b7 => {
                self.neon[29] &= !(0xff_u128 << (7 * 8));
                self.neon[29] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v29b8 => {
                self.neon[29] &= !(0xff_u128 << (8 * 8));
                self.neon[29] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v29b9 => {
                self.neon[29] &= !(0xff_u128 << (9 * 8));
                self.neon[29] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v29b10 => {
                self.neon[29] &= !(0xff_u128 << (10 * 8));
                self.neon[29] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v29b11 => {
                self.neon[29] &= !(0xff_u128 << (11 * 8));
                self.neon[29] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v29b12 => {
                self.neon[29] &= !(0xff_u128 << (12 * 8));
                self.neon[29] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v29b13 => {
                self.neon[29] &= !(0xff_u128 << (13 * 8));
                self.neon[29] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v29b14 => {
                self.neon[29] &= !(0xff_u128 << (14 * 8));
                self.neon[29] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v29b15 => {
                self.neon[29] &= !(0xff_u128 << (15 * 8));
                self.neon[29] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v30b0 => {
                self.neon[30] &= !(0xff_u128 << (0 * 8));
                self.neon[30] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v30b1 => {
                self.neon[30] &= !(0xff_u128 << (1 * 8));
                self.neon[30] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v30b2 => {
                self.neon[30] &= !(0xff_u128 << (2 * 8));
                self.neon[30] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v30b3 => {
                self.neon[30] &= !(0xff_u128 << (3 * 8));
                self.neon[30] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v30b4 => {
                self.neon[30] &= !(0xff_u128 << (4 * 8));
                self.neon[30] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v30b5 => {
                self.neon[30] &= !(0xff_u128 << (5 * 8));
                self.neon[30] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v30b6 => {
                self.neon[30] &= !(0xff_u128 << (6 * 8));
                self.neon[30] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v30b7 => {
                self.neon[30] &= !(0xff_u128 << (7 * 8));
                self.neon[30] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v30b8 => {
                self.neon[30] &= !(0xff_u128 << (8 * 8));
                self.neon[30] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v30b9 => {
                self.neon[30] &= !(0xff_u128 << (9 * 8));
                self.neon[30] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v30b10 => {
                self.neon[30] &= !(0xff_u128 << (10 * 8));
                self.neon[30] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v30b11 => {
                self.neon[30] &= !(0xff_u128 << (11 * 8));
                self.neon[30] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v30b12 => {
                self.neon[30] &= !(0xff_u128 << (12 * 8));
                self.neon[30] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v30b13 => {
                self.neon[30] &= !(0xff_u128 << (13 * 8));
                self.neon[30] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v30b14 => {
                self.neon[30] &= !(0xff_u128 << (14 * 8));
                self.neon[30] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v30b15 => {
                self.neon[30] &= !(0xff_u128 << (15 * 8));
                self.neon[30] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v31b0 => {
                self.neon[31] &= !(0xff_u128 << (0 * 8));
                self.neon[31] |= (value.get_byte() as u128) << (0 * 8);
            }
            Arm64Reg::v31b1 => {
                self.neon[31] &= !(0xff_u128 << (1 * 8));
                self.neon[31] |= (value.get_byte() as u128) << (1 * 8);
            }
            Arm64Reg::v31b2 => {
                self.neon[31] &= !(0xff_u128 << (2 * 8));
                self.neon[31] |= (value.get_byte() as u128) << (2 * 8);
            }
            Arm64Reg::v31b3 => {
                self.neon[31] &= !(0xff_u128 << (3 * 8));
                self.neon[31] |= (value.get_byte() as u128) << (3 * 8);
            }
            Arm64Reg::v31b4 => {
                self.neon[31] &= !(0xff_u128 << (4 * 8));
                self.neon[31] |= (value.get_byte() as u128) << (4 * 8);
            }
            Arm64Reg::v31b5 => {
                self.neon[31] &= !(0xff_u128 << (5 * 8));
                self.neon[31] |= (value.get_byte() as u128) << (5 * 8);
            }
            Arm64Reg::v31b6 => {
                self.neon[31] &= !(0xff_u128 << (6 * 8));
                self.neon[31] |= (value.get_byte() as u128) << (6 * 8);
            }
            Arm64Reg::v31b7 => {
                self.neon[31] &= !(0xff_u128 << (7 * 8));
                self.neon[31] |= (value.get_byte() as u128) << (7 * 8);
            }
            Arm64Reg::v31b8 => {
                self.neon[31] &= !(0xff_u128 << (8 * 8));
                self.neon[31] |= (value.get_byte() as u128) << (8 * 8);
            }
            Arm64Reg::v31b9 => {
                self.neon[31] &= !(0xff_u128 << (9 * 8));
                self.neon[31] |= (value.get_byte() as u128) << (9 * 8);
            }
            Arm64Reg::v31b10 => {
                self.neon[31] &= !(0xff_u128 << (10 * 8));
                self.neon[31] |= (value.get_byte() as u128) << (10 * 8);
            }
            Arm64Reg::v31b11 => {
                self.neon[31] &= !(0xff_u128 << (11 * 8));
                self.neon[31] |= (value.get_byte() as u128) << (11 * 8);
            }
            Arm64Reg::v31b12 => {
                self.neon[31] &= !(0xff_u128 << (12 * 8));
                self.neon[31] |= (value.get_byte() as u128) << (12 * 8);
            }
            Arm64Reg::v31b13 => {
                self.neon[31] &= !(0xff_u128 << (13 * 8));
                self.neon[31] |= (value.get_byte() as u128) << (13 * 8);
            }
            Arm64Reg::v31b14 => {
                self.neon[31] &= !(0xff_u128 << (14 * 8));
                self.neon[31] |= (value.get_byte() as u128) << (14 * 8);
            }
            Arm64Reg::v31b15 => {
                self.neon[31] &= !(0xff_u128 << (15 * 8));
                self.neon[31] |= (value.get_byte() as u128) << (15 * 8);
            }
            Arm64Reg::v0h0 => {
                self.neon[0] &= 0xffff_u128 << (16 * 0);
                self.neon[0] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v0h1 => {
                self.neon[0] &= 0xffff_u128 << (16 * 1);
                self.neon[0] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v0h2 => {
                self.neon[0] &= 0xffff_u128 << (16 * 2);
                self.neon[0] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v0h3 => {
                self.neon[0] &= 0xffff_u128 << (16 * 3);
                self.neon[0] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v0h4 => {
                self.neon[0] &= 0xffff_u128 << (16 * 4);
                self.neon[0] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v0h5 => {
                self.neon[0] &= 0xffff_u128 << (16 * 5);
                self.neon[0] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v0h6 => {
                self.neon[0] &= 0xffff_u128 << (16 * 6);
                self.neon[0] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v0h7 => {
                self.neon[0] &= 0xffff_u128 << (16 * 7);
                self.neon[0] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v1h0 => {
                self.neon[1] &= 0xffff_u128 << (16 * 0);
                self.neon[1] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v1h1 => {
                self.neon[1] &= 0xffff_u128 << (16 * 1);
                self.neon[1] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v1h2 => {
                self.neon[1] &= 0xffff_u128 << (16 * 2);
                self.neon[1] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v1h3 => {
                self.neon[1] &= 0xffff_u128 << (16 * 3);
                self.neon[1] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v1h4 => {
                self.neon[1] &= 0xffff_u128 << (16 * 4);
                self.neon[1] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v1h5 => {
                self.neon[1] &= 0xffff_u128 << (16 * 5);
                self.neon[1] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v1h6 => {
                self.neon[1] &= 0xffff_u128 << (16 * 6);
                self.neon[1] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v1h7 => {
                self.neon[1] &= 0xffff_u128 << (16 * 7);
                self.neon[1] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v2h0 => {
                self.neon[2] &= 0xffff_u128 << (16 * 0);
                self.neon[2] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v2h1 => {
                self.neon[2] &= 0xffff_u128 << (16 * 1);
                self.neon[2] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v2h2 => {
                self.neon[2] &= 0xffff_u128 << (16 * 2);
                self.neon[2] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v2h3 => {
                self.neon[2] &= 0xffff_u128 << (16 * 3);
                self.neon[2] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v2h4 => {
                self.neon[2] &= 0xffff_u128 << (16 * 4);
                self.neon[2] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v2h5 => {
                self.neon[2] &= 0xffff_u128 << (16 * 5);
                self.neon[2] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v2h6 => {
                self.neon[2] &= 0xffff_u128 << (16 * 6);
                self.neon[2] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v2h7 => {
                self.neon[2] &= 0xffff_u128 << (16 * 7);
                self.neon[2] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v3h0 => {
                self.neon[3] &= 0xffff_u128 << (16 * 0);
                self.neon[3] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v3h1 => {
                self.neon[3] &= 0xffff_u128 << (16 * 1);
                self.neon[3] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v3h2 => {
                self.neon[3] &= 0xffff_u128 << (16 * 2);
                self.neon[3] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v3h3 => {
                self.neon[3] &= 0xffff_u128 << (16 * 3);
                self.neon[3] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v3h4 => {
                self.neon[3] &= 0xffff_u128 << (16 * 4);
                self.neon[3] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v3h5 => {
                self.neon[3] &= 0xffff_u128 << (16 * 5);
                self.neon[3] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v3h6 => {
                self.neon[3] &= 0xffff_u128 << (16 * 6);
                self.neon[3] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v3h7 => {
                self.neon[3] &= 0xffff_u128 << (16 * 7);
                self.neon[3] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v4h0 => {
                self.neon[4] &= 0xffff_u128 << (16 * 0);
                self.neon[4] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v4h1 => {
                self.neon[4] &= 0xffff_u128 << (16 * 1);
                self.neon[4] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v4h2 => {
                self.neon[4] &= 0xffff_u128 << (16 * 2);
                self.neon[4] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v4h3 => {
                self.neon[4] &= 0xffff_u128 << (16 * 3);
                self.neon[4] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v4h4 => {
                self.neon[4] &= 0xffff_u128 << (16 * 4);
                self.neon[4] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v4h5 => {
                self.neon[4] &= 0xffff_u128 << (16 * 5);
                self.neon[4] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v4h6 => {
                self.neon[4] &= 0xffff_u128 << (16 * 6);
                self.neon[4] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v4h7 => {
                self.neon[4] &= 0xffff_u128 << (16 * 7);
                self.neon[4] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v5h0 => {
                self.neon[5] &= 0xffff_u128 << (16 * 0);
                self.neon[5] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v5h1 => {
                self.neon[5] &= 0xffff_u128 << (16 * 1);
                self.neon[5] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v5h2 => {
                self.neon[5] &= 0xffff_u128 << (16 * 2);
                self.neon[5] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v5h3 => {
                self.neon[5] &= 0xffff_u128 << (16 * 3);
                self.neon[5] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v5h4 => {
                self.neon[5] &= 0xffff_u128 << (16 * 4);
                self.neon[5] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v5h5 => {
                self.neon[5] &= 0xffff_u128 << (16 * 5);
                self.neon[5] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v5h6 => {
                self.neon[5] &= 0xffff_u128 << (16 * 6);
                self.neon[5] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v5h7 => {
                self.neon[5] &= 0xffff_u128 << (16 * 7);
                self.neon[5] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v6h0 => {
                self.neon[6] &= 0xffff_u128 << (16 * 0);
                self.neon[6] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v6h1 => {
                self.neon[6] &= 0xffff_u128 << (16 * 1);
                self.neon[6] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v6h2 => {
                self.neon[6] &= 0xffff_u128 << (16 * 2);
                self.neon[6] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v6h3 => {
                self.neon[6] &= 0xffff_u128 << (16 * 3);
                self.neon[6] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v6h4 => {
                self.neon[6] &= 0xffff_u128 << (16 * 4);
                self.neon[6] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v6h5 => {
                self.neon[6] &= 0xffff_u128 << (16 * 5);
                self.neon[6] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v6h6 => {
                self.neon[6] &= 0xffff_u128 << (16 * 6);
                self.neon[6] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v6h7 => {
                self.neon[6] &= 0xffff_u128 << (16 * 7);
                self.neon[6] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v7h0 => {
                self.neon[7] &= 0xffff_u128 << (16 * 0);
                self.neon[7] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v7h1 => {
                self.neon[7] &= 0xffff_u128 << (16 * 1);
                self.neon[7] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v7h2 => {
                self.neon[7] &= 0xffff_u128 << (16 * 2);
                self.neon[7] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v7h3 => {
                self.neon[7] &= 0xffff_u128 << (16 * 3);
                self.neon[7] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v7h4 => {
                self.neon[7] &= 0xffff_u128 << (16 * 4);
                self.neon[7] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v7h5 => {
                self.neon[7] &= 0xffff_u128 << (16 * 5);
                self.neon[7] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v7h6 => {
                self.neon[7] &= 0xffff_u128 << (16 * 6);
                self.neon[7] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v7h7 => {
                self.neon[7] &= 0xffff_u128 << (16 * 7);
                self.neon[7] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v8h0 => {
                self.neon[8] &= 0xffff_u128 << (16 * 0);
                self.neon[8] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v8h1 => {
                self.neon[8] &= 0xffff_u128 << (16 * 1);
                self.neon[8] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v8h2 => {
                self.neon[8] &= 0xffff_u128 << (16 * 2);
                self.neon[8] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v8h3 => {
                self.neon[8] &= 0xffff_u128 << (16 * 3);
                self.neon[8] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v8h4 => {
                self.neon[8] &= 0xffff_u128 << (16 * 4);
                self.neon[8] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v8h5 => {
                self.neon[8] &= 0xffff_u128 << (16 * 5);
                self.neon[8] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v8h6 => {
                self.neon[8] &= 0xffff_u128 << (16 * 6);
                self.neon[8] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v8h7 => {
                self.neon[8] &= 0xffff_u128 << (16 * 7);
                self.neon[8] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v9h0 => {
                self.neon[9] &= 0xffff_u128 << (16 * 0);
                self.neon[9] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v9h1 => {
                self.neon[9] &= 0xffff_u128 << (16 * 1);
                self.neon[9] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v9h2 => {
                self.neon[9] &= 0xffff_u128 << (16 * 2);
                self.neon[9] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v9h3 => {
                self.neon[9] &= 0xffff_u128 << (16 * 3);
                self.neon[9] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v9h4 => {
                self.neon[9] &= 0xffff_u128 << (16 * 4);
                self.neon[9] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v9h5 => {
                self.neon[9] &= 0xffff_u128 << (16 * 5);
                self.neon[9] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v9h6 => {
                self.neon[9] &= 0xffff_u128 << (16 * 6);
                self.neon[9] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v9h7 => {
                self.neon[9] &= 0xffff_u128 << (16 * 7);
                self.neon[9] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v10h0 => {
                self.neon[10] &= 0xffff_u128 << (16 * 0);
                self.neon[10] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v10h1 => {
                self.neon[10] &= 0xffff_u128 << (16 * 1);
                self.neon[10] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v10h2 => {
                self.neon[10] &= 0xffff_u128 << (16 * 2);
                self.neon[10] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v10h3 => {
                self.neon[10] &= 0xffff_u128 << (16 * 3);
                self.neon[10] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v10h4 => {
                self.neon[10] &= 0xffff_u128 << (16 * 4);
                self.neon[10] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v10h5 => {
                self.neon[10] &= 0xffff_u128 << (16 * 5);
                self.neon[10] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v10h6 => {
                self.neon[10] &= 0xffff_u128 << (16 * 6);
                self.neon[10] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v10h7 => {
                self.neon[10] &= 0xffff_u128 << (16 * 7);
                self.neon[10] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v11h0 => {
                self.neon[11] &= 0xffff_u128 << (16 * 0);
                self.neon[11] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v11h1 => {
                self.neon[11] &= 0xffff_u128 << (16 * 1);
                self.neon[11] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v11h2 => {
                self.neon[11] &= 0xffff_u128 << (16 * 2);
                self.neon[11] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v11h3 => {
                self.neon[11] &= 0xffff_u128 << (16 * 3);
                self.neon[11] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v11h4 => {
                self.neon[11] &= 0xffff_u128 << (16 * 4);
                self.neon[11] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v11h5 => {
                self.neon[11] &= 0xffff_u128 << (16 * 5);
                self.neon[11] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v11h6 => {
                self.neon[11] &= 0xffff_u128 << (16 * 6);
                self.neon[11] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v11h7 => {
                self.neon[11] &= 0xffff_u128 << (16 * 7);
                self.neon[11] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v12h0 => {
                self.neon[12] &= 0xffff_u128 << (16 * 0);
                self.neon[12] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v12h1 => {
                self.neon[12] &= 0xffff_u128 << (16 * 1);
                self.neon[12] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v12h2 => {
                self.neon[12] &= 0xffff_u128 << (16 * 2);
                self.neon[12] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v12h3 => {
                self.neon[12] &= 0xffff_u128 << (16 * 3);
                self.neon[12] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v12h4 => {
                self.neon[12] &= 0xffff_u128 << (16 * 4);
                self.neon[12] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v12h5 => {
                self.neon[12] &= 0xffff_u128 << (16 * 5);
                self.neon[12] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v12h6 => {
                self.neon[12] &= 0xffff_u128 << (16 * 6);
                self.neon[12] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v12h7 => {
                self.neon[12] &= 0xffff_u128 << (16 * 7);
                self.neon[12] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v13h0 => {
                self.neon[13] &= 0xffff_u128 << (16 * 0);
                self.neon[13] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v13h1 => {
                self.neon[13] &= 0xffff_u128 << (16 * 1);
                self.neon[13] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v13h2 => {
                self.neon[13] &= 0xffff_u128 << (16 * 2);
                self.neon[13] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v13h3 => {
                self.neon[13] &= 0xffff_u128 << (16 * 3);
                self.neon[13] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v13h4 => {
                self.neon[13] &= 0xffff_u128 << (16 * 4);
                self.neon[13] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v13h5 => {
                self.neon[13] &= 0xffff_u128 << (16 * 5);
                self.neon[13] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v13h6 => {
                self.neon[13] &= 0xffff_u128 << (16 * 6);
                self.neon[13] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v13h7 => {
                self.neon[13] &= 0xffff_u128 << (16 * 7);
                self.neon[13] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v14h0 => {
                self.neon[14] &= 0xffff_u128 << (16 * 0);
                self.neon[14] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v14h1 => {
                self.neon[14] &= 0xffff_u128 << (16 * 1);
                self.neon[14] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v14h2 => {
                self.neon[14] &= 0xffff_u128 << (16 * 2);
                self.neon[14] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v14h3 => {
                self.neon[14] &= 0xffff_u128 << (16 * 3);
                self.neon[14] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v14h4 => {
                self.neon[14] &= 0xffff_u128 << (16 * 4);
                self.neon[14] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v14h5 => {
                self.neon[14] &= 0xffff_u128 << (16 * 5);
                self.neon[14] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v14h6 => {
                self.neon[14] &= 0xffff_u128 << (16 * 6);
                self.neon[14] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v14h7 => {
                self.neon[14] &= 0xffff_u128 << (16 * 7);
                self.neon[14] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v15h0 => {
                self.neon[15] &= 0xffff_u128 << (16 * 0);
                self.neon[15] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v15h1 => {
                self.neon[15] &= 0xffff_u128 << (16 * 1);
                self.neon[15] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v15h2 => {
                self.neon[15] &= 0xffff_u128 << (16 * 2);
                self.neon[15] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v15h3 => {
                self.neon[15] &= 0xffff_u128 << (16 * 3);
                self.neon[15] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v15h4 => {
                self.neon[15] &= 0xffff_u128 << (16 * 4);
                self.neon[15] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v15h5 => {
                self.neon[15] &= 0xffff_u128 << (16 * 5);
                self.neon[15] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v15h6 => {
                self.neon[15] &= 0xffff_u128 << (16 * 6);
                self.neon[15] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v15h7 => {
                self.neon[15] &= 0xffff_u128 << (16 * 7);
                self.neon[15] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v16h0 => {
                self.neon[16] &= 0xffff_u128 << (16 * 0);
                self.neon[16] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v16h1 => {
                self.neon[16] &= 0xffff_u128 << (16 * 1);
                self.neon[16] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v16h2 => {
                self.neon[16] &= 0xffff_u128 << (16 * 2);
                self.neon[16] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v16h3 => {
                self.neon[16] &= 0xffff_u128 << (16 * 3);
                self.neon[16] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v16h4 => {
                self.neon[16] &= 0xffff_u128 << (16 * 4);
                self.neon[16] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v16h5 => {
                self.neon[16] &= 0xffff_u128 << (16 * 5);
                self.neon[16] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v16h6 => {
                self.neon[16] &= 0xffff_u128 << (16 * 6);
                self.neon[16] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v16h7 => {
                self.neon[16] &= 0xffff_u128 << (16 * 7);
                self.neon[16] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v17h0 => {
                self.neon[17] &= 0xffff_u128 << (16 * 0);
                self.neon[17] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v17h1 => {
                self.neon[17] &= 0xffff_u128 << (16 * 1);
                self.neon[17] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v17h2 => {
                self.neon[17] &= 0xffff_u128 << (16 * 2);
                self.neon[17] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v17h3 => {
                self.neon[17] &= 0xffff_u128 << (16 * 3);
                self.neon[17] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v17h4 => {
                self.neon[17] &= 0xffff_u128 << (16 * 4);
                self.neon[17] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v17h5 => {
                self.neon[17] &= 0xffff_u128 << (16 * 5);
                self.neon[17] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v17h6 => {
                self.neon[17] &= 0xffff_u128 << (16 * 6);
                self.neon[17] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v17h7 => {
                self.neon[17] &= 0xffff_u128 << (16 * 7);
                self.neon[17] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v18h0 => {
                self.neon[18] &= 0xffff_u128 << (16 * 0);
                self.neon[18] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v18h1 => {
                self.neon[18] &= 0xffff_u128 << (16 * 1);
                self.neon[18] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v18h2 => {
                self.neon[18] &= 0xffff_u128 << (16 * 2);
                self.neon[18] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v18h3 => {
                self.neon[18] &= 0xffff_u128 << (16 * 3);
                self.neon[18] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v18h4 => {
                self.neon[18] &= 0xffff_u128 << (16 * 4);
                self.neon[18] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v18h5 => {
                self.neon[18] &= 0xffff_u128 << (16 * 5);
                self.neon[18] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v18h6 => {
                self.neon[18] &= 0xffff_u128 << (16 * 6);
                self.neon[18] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v18h7 => {
                self.neon[18] &= 0xffff_u128 << (16 * 7);
                self.neon[18] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v19h0 => {
                self.neon[19] &= 0xffff_u128 << (16 * 0);
                self.neon[19] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v19h1 => {
                self.neon[19] &= 0xffff_u128 << (16 * 1);
                self.neon[19] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v19h2 => {
                self.neon[19] &= 0xffff_u128 << (16 * 2);
                self.neon[19] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v19h3 => {
                self.neon[19] &= 0xffff_u128 << (16 * 3);
                self.neon[19] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v19h4 => {
                self.neon[19] &= 0xffff_u128 << (16 * 4);
                self.neon[19] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v19h5 => {
                self.neon[19] &= 0xffff_u128 << (16 * 5);
                self.neon[19] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v19h6 => {
                self.neon[19] &= 0xffff_u128 << (16 * 6);
                self.neon[19] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v19h7 => {
                self.neon[19] &= 0xffff_u128 << (16 * 7);
                self.neon[19] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v20h0 => {
                self.neon[20] &= 0xffff_u128 << (16 * 0);
                self.neon[20] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v20h1 => {
                self.neon[20] &= 0xffff_u128 << (16 * 1);
                self.neon[20] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v20h2 => {
                self.neon[20] &= 0xffff_u128 << (16 * 2);
                self.neon[20] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v20h3 => {
                self.neon[20] &= 0xffff_u128 << (16 * 3);
                self.neon[20] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v20h4 => {
                self.neon[20] &= 0xffff_u128 << (16 * 4);
                self.neon[20] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v20h5 => {
                self.neon[20] &= 0xffff_u128 << (16 * 5);
                self.neon[20] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v20h6 => {
                self.neon[20] &= 0xffff_u128 << (16 * 6);
                self.neon[20] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v20h7 => {
                self.neon[20] &= 0xffff_u128 << (16 * 7);
                self.neon[20] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v21h0 => {
                self.neon[21] &= 0xffff_u128 << (16 * 0);
                self.neon[21] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v21h1 => {
                self.neon[21] &= 0xffff_u128 << (16 * 1);
                self.neon[21] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v21h2 => {
                self.neon[21] &= 0xffff_u128 << (16 * 2);
                self.neon[21] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v21h3 => {
                self.neon[21] &= 0xffff_u128 << (16 * 3);
                self.neon[21] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v21h4 => {
                self.neon[21] &= 0xffff_u128 << (16 * 4);
                self.neon[21] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v21h5 => {
                self.neon[21] &= 0xffff_u128 << (16 * 5);
                self.neon[21] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v21h6 => {
                self.neon[21] &= 0xffff_u128 << (16 * 6);
                self.neon[21] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v21h7 => {
                self.neon[21] &= 0xffff_u128 << (16 * 7);
                self.neon[21] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v22h0 => {
                self.neon[22] &= 0xffff_u128 << (16 * 0);
                self.neon[22] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v22h1 => {
                self.neon[22] &= 0xffff_u128 << (16 * 1);
                self.neon[22] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v22h2 => {
                self.neon[22] &= 0xffff_u128 << (16 * 2);
                self.neon[22] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v22h3 => {
                self.neon[22] &= 0xffff_u128 << (16 * 3);
                self.neon[22] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v22h4 => {
                self.neon[22] &= 0xffff_u128 << (16 * 4);
                self.neon[22] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v22h5 => {
                self.neon[22] &= 0xffff_u128 << (16 * 5);
                self.neon[22] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v22h6 => {
                self.neon[22] &= 0xffff_u128 << (16 * 6);
                self.neon[22] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v22h7 => {
                self.neon[22] &= 0xffff_u128 << (16 * 7);
                self.neon[22] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v23h0 => {
                self.neon[23] &= 0xffff_u128 << (16 * 0);
                self.neon[23] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v23h1 => {
                self.neon[23] &= 0xffff_u128 << (16 * 1);
                self.neon[23] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v23h2 => {
                self.neon[23] &= 0xffff_u128 << (16 * 2);
                self.neon[23] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v23h3 => {
                self.neon[23] &= 0xffff_u128 << (16 * 3);
                self.neon[23] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v23h4 => {
                self.neon[23] &= 0xffff_u128 << (16 * 4);
                self.neon[23] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v23h5 => {
                self.neon[23] &= 0xffff_u128 << (16 * 5);
                self.neon[23] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v23h6 => {
                self.neon[23] &= 0xffff_u128 << (16 * 6);
                self.neon[23] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v23h7 => {
                self.neon[23] &= 0xffff_u128 << (16 * 7);
                self.neon[23] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v24h0 => {
                self.neon[24] &= 0xffff_u128 << (16 * 0);
                self.neon[24] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v24h1 => {
                self.neon[24] &= 0xffff_u128 << (16 * 1);
                self.neon[24] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v24h2 => {
                self.neon[24] &= 0xffff_u128 << (16 * 2);
                self.neon[24] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v24h3 => {
                self.neon[24] &= 0xffff_u128 << (16 * 3);
                self.neon[24] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v24h4 => {
                self.neon[24] &= 0xffff_u128 << (16 * 4);
                self.neon[24] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v24h5 => {
                self.neon[24] &= 0xffff_u128 << (16 * 5);
                self.neon[24] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v24h6 => {
                self.neon[24] &= 0xffff_u128 << (16 * 6);
                self.neon[24] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v24h7 => {
                self.neon[24] &= 0xffff_u128 << (16 * 7);
                self.neon[24] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v25h0 => {
                self.neon[25] &= 0xffff_u128 << (16 * 0);
                self.neon[25] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v25h1 => {
                self.neon[25] &= 0xffff_u128 << (16 * 1);
                self.neon[25] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v25h2 => {
                self.neon[25] &= 0xffff_u128 << (16 * 2);
                self.neon[25] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v25h3 => {
                self.neon[25] &= 0xffff_u128 << (16 * 3);
                self.neon[25] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v25h4 => {
                self.neon[25] &= 0xffff_u128 << (16 * 4);
                self.neon[25] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v25h5 => {
                self.neon[25] &= 0xffff_u128 << (16 * 5);
                self.neon[25] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v25h6 => {
                self.neon[25] &= 0xffff_u128 << (16 * 6);
                self.neon[25] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v25h7 => {
                self.neon[25] &= 0xffff_u128 << (16 * 7);
                self.neon[25] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v26h0 => {
                self.neon[26] &= 0xffff_u128 << (16 * 0);
                self.neon[26] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v26h1 => {
                self.neon[26] &= 0xffff_u128 << (16 * 1);
                self.neon[26] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v26h2 => {
                self.neon[26] &= 0xffff_u128 << (16 * 2);
                self.neon[26] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v26h3 => {
                self.neon[26] &= 0xffff_u128 << (16 * 3);
                self.neon[26] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v26h4 => {
                self.neon[26] &= 0xffff_u128 << (16 * 4);
                self.neon[26] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v26h5 => {
                self.neon[26] &= 0xffff_u128 << (16 * 5);
                self.neon[26] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v26h6 => {
                self.neon[26] &= 0xffff_u128 << (16 * 6);
                self.neon[26] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v26h7 => {
                self.neon[26] &= 0xffff_u128 << (16 * 7);
                self.neon[26] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v27h0 => {
                self.neon[27] &= 0xffff_u128 << (16 * 0);
                self.neon[27] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v27h1 => {
                self.neon[27] &= 0xffff_u128 << (16 * 1);
                self.neon[27] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v27h2 => {
                self.neon[27] &= 0xffff_u128 << (16 * 2);
                self.neon[27] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v27h3 => {
                self.neon[27] &= 0xffff_u128 << (16 * 3);
                self.neon[27] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v27h4 => {
                self.neon[27] &= 0xffff_u128 << (16 * 4);
                self.neon[27] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v27h5 => {
                self.neon[27] &= 0xffff_u128 << (16 * 5);
                self.neon[27] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v27h6 => {
                self.neon[27] &= 0xffff_u128 << (16 * 6);
                self.neon[27] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v27h7 => {
                self.neon[27] &= 0xffff_u128 << (16 * 7);
                self.neon[27] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v28h0 => {
                self.neon[28] &= 0xffff_u128 << (16 * 0);
                self.neon[28] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v28h1 => {
                self.neon[28] &= 0xffff_u128 << (16 * 1);
                self.neon[28] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v28h2 => {
                self.neon[28] &= 0xffff_u128 << (16 * 2);
                self.neon[28] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v28h3 => {
                self.neon[28] &= 0xffff_u128 << (16 * 3);
                self.neon[28] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v28h4 => {
                self.neon[28] &= 0xffff_u128 << (16 * 4);
                self.neon[28] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v28h5 => {
                self.neon[28] &= 0xffff_u128 << (16 * 5);
                self.neon[28] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v28h6 => {
                self.neon[28] &= 0xffff_u128 << (16 * 6);
                self.neon[28] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v28h7 => {
                self.neon[28] &= 0xffff_u128 << (16 * 7);
                self.neon[28] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v29h0 => {
                self.neon[29] &= 0xffff_u128 << (16 * 0);
                self.neon[29] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v29h1 => {
                self.neon[29] &= 0xffff_u128 << (16 * 1);
                self.neon[29] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v29h2 => {
                self.neon[29] &= 0xffff_u128 << (16 * 2);
                self.neon[29] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v29h3 => {
                self.neon[29] &= 0xffff_u128 << (16 * 3);
                self.neon[29] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v29h4 => {
                self.neon[29] &= 0xffff_u128 << (16 * 4);
                self.neon[29] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v29h5 => {
                self.neon[29] &= 0xffff_u128 << (16 * 5);
                self.neon[29] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v29h6 => {
                self.neon[29] &= 0xffff_u128 << (16 * 6);
                self.neon[29] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v29h7 => {
                self.neon[29] &= 0xffff_u128 << (16 * 7);
                self.neon[29] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v30h0 => {
                self.neon[30] &= 0xffff_u128 << (16 * 0);
                self.neon[30] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v30h1 => {
                self.neon[30] &= 0xffff_u128 << (16 * 1);
                self.neon[30] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v30h2 => {
                self.neon[30] &= 0xffff_u128 << (16 * 2);
                self.neon[30] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v30h3 => {
                self.neon[30] &= 0xffff_u128 << (16 * 3);
                self.neon[30] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v30h4 => {
                self.neon[30] &= 0xffff_u128 << (16 * 4);
                self.neon[30] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v30h5 => {
                self.neon[30] &= 0xffff_u128 << (16 * 5);
                self.neon[30] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v30h6 => {
                self.neon[30] &= 0xffff_u128 << (16 * 6);
                self.neon[30] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v30h7 => {
                self.neon[30] &= 0xffff_u128 << (16 * 7);
                self.neon[30] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v31h0 => {
                self.neon[31] &= 0xffff_u128 << (16 * 0);
                self.neon[31] |= (value.get_short() as u128) << (16 * 0);
            }
            Arm64Reg::v31h1 => {
                self.neon[31] &= 0xffff_u128 << (16 * 1);
                self.neon[31] |= (value.get_short() as u128) << (16 * 1);
            }
            Arm64Reg::v31h2 => {
                self.neon[31] &= 0xffff_u128 << (16 * 2);
                self.neon[31] |= (value.get_short() as u128) << (16 * 2);
            }
            Arm64Reg::v31h3 => {
                self.neon[31] &= 0xffff_u128 << (16 * 3);
                self.neon[31] |= (value.get_short() as u128) << (16 * 3);
            }
            Arm64Reg::v31h4 => {
                self.neon[31] &= 0xffff_u128 << (16 * 4);
                self.neon[31] |= (value.get_short() as u128) << (16 * 4);
            }
            Arm64Reg::v31h5 => {
                self.neon[31] &= 0xffff_u128 << (16 * 5);
                self.neon[31] |= (value.get_short() as u128) << (16 * 5);
            }
            Arm64Reg::v31h6 => {
                self.neon[31] &= 0xffff_u128 << (16 * 6);
                self.neon[31] |= (value.get_short() as u128) << (16 * 6);
            }
            Arm64Reg::v31h7 => {
                self.neon[31] &= 0xffff_u128 << (16 * 7);
                self.neon[31] |= (value.get_short() as u128) << (16 * 7);
            }
            Arm64Reg::v0s0 => {
                self.neon[0] &= 0xffffffff_u128 << (32 * 0);
                self.neon[0] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v0s1 => {
                self.neon[0] &= 0xffffffff_u128 << (32 * 1);
                self.neon[0] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v0s2 => {
                self.neon[0] &= 0xffffffff_u128 << (32 * 2);
                self.neon[0] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v0s3 => {
                self.neon[0] &= 0xffffffff_u128 << (32 * 3);
                self.neon[0] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v1s0 => {
                self.neon[1] &= 0xffffffff_u128 << (32 * 0);
                self.neon[1] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v1s1 => {
                self.neon[1] &= 0xffffffff_u128 << (32 * 1);
                self.neon[1] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v1s2 => {
                self.neon[1] &= 0xffffffff_u128 << (32 * 2);
                self.neon[1] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v1s3 => {
                self.neon[1] &= 0xffffffff_u128 << (32 * 3);
                self.neon[1] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v2s0 => {
                self.neon[2] &= 0xffffffff_u128 << (32 * 0);
                self.neon[2] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v2s1 => {
                self.neon[2] &= 0xffffffff_u128 << (32 * 1);
                self.neon[2] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v2s2 => {
                self.neon[2] &= 0xffffffff_u128 << (32 * 2);
                self.neon[2] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v2s3 => {
                self.neon[2] &= 0xffffffff_u128 << (32 * 3);
                self.neon[2] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v3s0 => {
                self.neon[3] &= 0xffffffff_u128 << (32 * 0);
                self.neon[3] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v3s1 => {
                self.neon[3] &= 0xffffffff_u128 << (32 * 1);
                self.neon[3] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v3s2 => {
                self.neon[3] &= 0xffffffff_u128 << (32 * 2);
                self.neon[3] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v3s3 => {
                self.neon[3] &= 0xffffffff_u128 << (32 * 3);
                self.neon[3] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v4s0 => {
                self.neon[4] &= 0xffffffff_u128 << (32 * 0);
                self.neon[4] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v4s1 => {
                self.neon[4] &= 0xffffffff_u128 << (32 * 1);
                self.neon[4] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v4s2 => {
                self.neon[4] &= 0xffffffff_u128 << (32 * 2);
                self.neon[4] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v4s3 => {
                self.neon[4] &= 0xffffffff_u128 << (32 * 3);
                self.neon[4] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v5s0 => {
                self.neon[5] &= 0xffffffff_u128 << (32 * 0);
                self.neon[5] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v5s1 => {
                self.neon[5] &= 0xffffffff_u128 << (32 * 1);
                self.neon[5] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v5s2 => {
                self.neon[5] &= 0xffffffff_u128 << (32 * 2);
                self.neon[5] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v5s3 => {
                self.neon[5] &= 0xffffffff_u128 << (32 * 3);
                self.neon[5] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v6s0 => {
                self.neon[6] &= 0xffffffff_u128 << (32 * 0);
                self.neon[6] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v6s1 => {
                self.neon[6] &= 0xffffffff_u128 << (32 * 1);
                self.neon[6] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v6s2 => {
                self.neon[6] &= 0xffffffff_u128 << (32 * 2);
                self.neon[6] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v6s3 => {
                self.neon[6] &= 0xffffffff_u128 << (32 * 3);
                self.neon[6] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v7s0 => {
                self.neon[7] &= 0xffffffff_u128 << (32 * 0);
                self.neon[7] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v7s1 => {
                self.neon[7] &= 0xffffffff_u128 << (32 * 1);
                self.neon[7] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v7s2 => {
                self.neon[7] &= 0xffffffff_u128 << (32 * 2);
                self.neon[7] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v7s3 => {
                self.neon[7] &= 0xffffffff_u128 << (32 * 3);
                self.neon[7] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v8s0 => {
                self.neon[8] &= 0xffffffff_u128 << (32 * 0);
                self.neon[8] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v8s1 => {
                self.neon[8] &= 0xffffffff_u128 << (32 * 1);
                self.neon[8] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v8s2 => {
                self.neon[8] &= 0xffffffff_u128 << (32 * 2);
                self.neon[8] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v8s3 => {
                self.neon[8] &= 0xffffffff_u128 << (32 * 3);
                self.neon[8] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v9s0 => {
                self.neon[9] &= 0xffffffff_u128 << (32 * 0);
                self.neon[9] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v9s1 => {
                self.neon[9] &= 0xffffffff_u128 << (32 * 1);
                self.neon[9] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v9s2 => {
                self.neon[9] &= 0xffffffff_u128 << (32 * 2);
                self.neon[9] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v9s3 => {
                self.neon[9] &= 0xffffffff_u128 << (32 * 3);
                self.neon[9] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v10s0 => {
                self.neon[10] &= 0xffffffff_u128 << (32 * 0);
                self.neon[10] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v10s1 => {
                self.neon[10] &= 0xffffffff_u128 << (32 * 1);
                self.neon[10] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v10s2 => {
                self.neon[10] &= 0xffffffff_u128 << (32 * 2);
                self.neon[10] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v10s3 => {
                self.neon[10] &= 0xffffffff_u128 << (32 * 3);
                self.neon[10] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v11s0 => {
                self.neon[11] &= 0xffffffff_u128 << (32 * 0);
                self.neon[11] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v11s1 => {
                self.neon[11] &= 0xffffffff_u128 << (32 * 1);
                self.neon[11] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v11s2 => {
                self.neon[11] &= 0xffffffff_u128 << (32 * 2);
                self.neon[11] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v11s3 => {
                self.neon[11] &= 0xffffffff_u128 << (32 * 3);
                self.neon[11] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v12s0 => {
                self.neon[12] &= 0xffffffff_u128 << (32 * 0);
                self.neon[12] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v12s1 => {
                self.neon[12] &= 0xffffffff_u128 << (32 * 1);
                self.neon[12] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v12s2 => {
                self.neon[12] &= 0xffffffff_u128 << (32 * 2);
                self.neon[12] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v12s3 => {
                self.neon[12] &= 0xffffffff_u128 << (32 * 3);
                self.neon[12] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v13s0 => {
                self.neon[13] &= 0xffffffff_u128 << (32 * 0);
                self.neon[13] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v13s1 => {
                self.neon[13] &= 0xffffffff_u128 << (32 * 1);
                self.neon[13] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v13s2 => {
                self.neon[13] &= 0xffffffff_u128 << (32 * 2);
                self.neon[13] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v13s3 => {
                self.neon[13] &= 0xffffffff_u128 << (32 * 3);
                self.neon[13] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v14s0 => {
                self.neon[14] &= 0xffffffff_u128 << (32 * 0);
                self.neon[14] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v14s1 => {
                self.neon[14] &= 0xffffffff_u128 << (32 * 1);
                self.neon[14] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v14s2 => {
                self.neon[14] &= 0xffffffff_u128 << (32 * 2);
                self.neon[14] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v14s3 => {
                self.neon[14] &= 0xffffffff_u128 << (32 * 3);
                self.neon[14] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v15s0 => {
                self.neon[15] &= 0xffffffff_u128 << (32 * 0);
                self.neon[15] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v15s1 => {
                self.neon[15] &= 0xffffffff_u128 << (32 * 1);
                self.neon[15] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v15s2 => {
                self.neon[15] &= 0xffffffff_u128 << (32 * 2);
                self.neon[15] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v15s3 => {
                self.neon[15] &= 0xffffffff_u128 << (32 * 3);
                self.neon[15] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v16s0 => {
                self.neon[16] &= 0xffffffff_u128 << (32 * 0);
                self.neon[16] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v16s1 => {
                self.neon[16] &= 0xffffffff_u128 << (32 * 1);
                self.neon[16] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v16s2 => {
                self.neon[16] &= 0xffffffff_u128 << (32 * 2);
                self.neon[16] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v16s3 => {
                self.neon[16] &= 0xffffffff_u128 << (32 * 3);
                self.neon[16] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v17s0 => {
                self.neon[17] &= 0xffffffff_u128 << (32 * 0);
                self.neon[17] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v17s1 => {
                self.neon[17] &= 0xffffffff_u128 << (32 * 1);
                self.neon[17] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v17s2 => {
                self.neon[17] &= 0xffffffff_u128 << (32 * 2);
                self.neon[17] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v17s3 => {
                self.neon[17] &= 0xffffffff_u128 << (32 * 3);
                self.neon[17] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v18s0 => {
                self.neon[18] &= 0xffffffff_u128 << (32 * 0);
                self.neon[18] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v18s1 => {
                self.neon[18] &= 0xffffffff_u128 << (32 * 1);
                self.neon[18] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v18s2 => {
                self.neon[18] &= 0xffffffff_u128 << (32 * 2);
                self.neon[18] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v18s3 => {
                self.neon[18] &= 0xffffffff_u128 << (32 * 3);
                self.neon[18] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v19s0 => {
                self.neon[19] &= 0xffffffff_u128 << (32 * 0);
                self.neon[19] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v19s1 => {
                self.neon[19] &= 0xffffffff_u128 << (32 * 1);
                self.neon[19] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v19s2 => {
                self.neon[19] &= 0xffffffff_u128 << (32 * 2);
                self.neon[19] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v19s3 => {
                self.neon[19] &= 0xffffffff_u128 << (32 * 3);
                self.neon[19] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v20s0 => {
                self.neon[20] &= 0xffffffff_u128 << (32 * 0);
                self.neon[20] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v20s1 => {
                self.neon[20] &= 0xffffffff_u128 << (32 * 1);
                self.neon[20] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v20s2 => {
                self.neon[20] &= 0xffffffff_u128 << (32 * 2);
                self.neon[20] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v20s3 => {
                self.neon[20] &= 0xffffffff_u128 << (32 * 3);
                self.neon[20] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v21s0 => {
                self.neon[21] &= 0xffffffff_u128 << (32 * 0);
                self.neon[21] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v21s1 => {
                self.neon[21] &= 0xffffffff_u128 << (32 * 1);
                self.neon[21] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v21s2 => {
                self.neon[21] &= 0xffffffff_u128 << (32 * 2);
                self.neon[21] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v21s3 => {
                self.neon[21] &= 0xffffffff_u128 << (32 * 3);
                self.neon[21] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v22s0 => {
                self.neon[22] &= 0xffffffff_u128 << (32 * 0);
                self.neon[22] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v22s1 => {
                self.neon[22] &= 0xffffffff_u128 << (32 * 1);
                self.neon[22] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v22s2 => {
                self.neon[22] &= 0xffffffff_u128 << (32 * 2);
                self.neon[22] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v22s3 => {
                self.neon[22] &= 0xffffffff_u128 << (32 * 3);
                self.neon[22] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v23s0 => {
                self.neon[23] &= 0xffffffff_u128 << (32 * 0);
                self.neon[23] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v23s1 => {
                self.neon[23] &= 0xffffffff_u128 << (32 * 1);
                self.neon[23] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v23s2 => {
                self.neon[23] &= 0xffffffff_u128 << (32 * 2);
                self.neon[23] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v23s3 => {
                self.neon[23] &= 0xffffffff_u128 << (32 * 3);
                self.neon[23] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v24s0 => {
                self.neon[24] &= 0xffffffff_u128 << (32 * 0);
                self.neon[24] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v24s1 => {
                self.neon[24] &= 0xffffffff_u128 << (32 * 1);
                self.neon[24] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v24s2 => {
                self.neon[24] &= 0xffffffff_u128 << (32 * 2);
                self.neon[24] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v24s3 => {
                self.neon[24] &= 0xffffffff_u128 << (32 * 3);
                self.neon[24] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v25s0 => {
                self.neon[25] &= 0xffffffff_u128 << (32 * 0);
                self.neon[25] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v25s1 => {
                self.neon[25] &= 0xffffffff_u128 << (32 * 1);
                self.neon[25] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v25s2 => {
                self.neon[25] &= 0xffffffff_u128 << (32 * 2);
                self.neon[25] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v25s3 => {
                self.neon[25] &= 0xffffffff_u128 << (32 * 3);
                self.neon[25] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v26s0 => {
                self.neon[26] &= 0xffffffff_u128 << (32 * 0);
                self.neon[26] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v26s1 => {
                self.neon[26] &= 0xffffffff_u128 << (32 * 1);
                self.neon[26] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v26s2 => {
                self.neon[26] &= 0xffffffff_u128 << (32 * 2);
                self.neon[26] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v26s3 => {
                self.neon[26] &= 0xffffffff_u128 << (32 * 3);
                self.neon[26] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v27s0 => {
                self.neon[27] &= 0xffffffff_u128 << (32 * 0);
                self.neon[27] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v27s1 => {
                self.neon[27] &= 0xffffffff_u128 << (32 * 1);
                self.neon[27] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v27s2 => {
                self.neon[27] &= 0xffffffff_u128 << (32 * 2);
                self.neon[27] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v27s3 => {
                self.neon[27] &= 0xffffffff_u128 << (32 * 3);
                self.neon[27] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v28s0 => {
                self.neon[28] &= 0xffffffff_u128 << (32 * 0);
                self.neon[28] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v28s1 => {
                self.neon[28] &= 0xffffffff_u128 << (32 * 1);
                self.neon[28] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v28s2 => {
                self.neon[28] &= 0xffffffff_u128 << (32 * 2);
                self.neon[28] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v28s3 => {
                self.neon[28] &= 0xffffffff_u128 << (32 * 3);
                self.neon[28] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v29s0 => {
                self.neon[29] &= 0xffffffff_u128 << (32 * 0);
                self.neon[29] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v29s1 => {
                self.neon[29] &= 0xffffffff_u128 << (32 * 1);
                self.neon[29] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v29s2 => {
                self.neon[29] &= 0xffffffff_u128 << (32 * 2);
                self.neon[29] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v29s3 => {
                self.neon[29] &= 0xffffffff_u128 << (32 * 3);
                self.neon[29] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v30s0 => {
                self.neon[30] &= 0xffffffff_u128 << (32 * 0);
                self.neon[30] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v30s1 => {
                self.neon[30] &= 0xffffffff_u128 << (32 * 1);
                self.neon[30] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v30s2 => {
                self.neon[30] &= 0xffffffff_u128 << (32 * 2);
                self.neon[30] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v30s3 => {
                self.neon[30] &= 0xffffffff_u128 << (32 * 3);
                self.neon[30] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v31s0 => {
                self.neon[31] &= 0xffffffff_u128 << (32 * 0);
                self.neon[31] |= (value.get_word() as u128) << (32 * 0);
            }
            Arm64Reg::v31s1 => {
                self.neon[31] &= 0xffffffff_u128 << (32 * 1);
                self.neon[31] |= (value.get_word() as u128) << (32 * 1);
            }
            Arm64Reg::v31s2 => {
                self.neon[31] &= 0xffffffff_u128 << (32 * 2);
                self.neon[31] |= (value.get_word() as u128) << (32 * 2);
            }
            Arm64Reg::v31s3 => {
                self.neon[31] &= 0xffffffff_u128 << (32 * 3);
                self.neon[31] |= (value.get_word() as u128) << (32 * 3);
            }
            Arm64Reg::v0d0 => {
                self.neon[0] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[0] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v0d1 => {
                self.neon[0] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[0] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v1d0 => {
                self.neon[1] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[1] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v1d1 => {
                self.neon[1] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[1] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v2d0 => {
                self.neon[2] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[2] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v2d1 => {
                self.neon[2] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[2] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v3d0 => {
                self.neon[3] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[3] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v3d1 => {
                self.neon[3] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[3] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v4d0 => {
                self.neon[4] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[4] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v4d1 => {
                self.neon[4] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[4] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v5d0 => {
                self.neon[5] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[5] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v5d1 => {
                self.neon[5] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[5] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v6d0 => {
                self.neon[6] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[6] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v6d1 => {
                self.neon[6] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[6] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v7d0 => {
                self.neon[7] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[7] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v7d1 => {
                self.neon[7] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[7] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v8d0 => {
                self.neon[8] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[8] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v8d1 => {
                self.neon[8] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[8] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v9d0 => {
                self.neon[9] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[9] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v9d1 => {
                self.neon[9] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[9] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v10d0 => {
                self.neon[10] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[10] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v10d1 => {
                self.neon[10] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[10] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v11d0 => {
                self.neon[11] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[11] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v11d1 => {
                self.neon[11] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[11] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v12d0 => {
                self.neon[12] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[12] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v12d1 => {
                self.neon[12] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[12] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v13d0 => {
                self.neon[13] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[13] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v13d1 => {
                self.neon[13] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[13] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v14d0 => {
                self.neon[14] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[14] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v14d1 => {
                self.neon[14] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[14] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v15d0 => {
                self.neon[15] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[15] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v15d1 => {
                self.neon[15] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[15] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v16d0 => {
                self.neon[16] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[16] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v16d1 => {
                self.neon[16] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[16] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v17d0 => {
                self.neon[17] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[17] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v17d1 => {
                self.neon[17] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[17] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v18d0 => {
                self.neon[18] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[18] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v18d1 => {
                self.neon[18] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[18] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v19d0 => {
                self.neon[19] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[19] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v19d1 => {
                self.neon[19] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[19] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v20d0 => {
                self.neon[20] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[20] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v20d1 => {
                self.neon[20] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[20] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v21d0 => {
                self.neon[21] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[21] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v21d1 => {
                self.neon[21] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[21] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v22d0 => {
                self.neon[22] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[22] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v22d1 => {
                self.neon[22] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[22] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v23d0 => {
                self.neon[23] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[23] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v23d1 => {
                self.neon[23] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[23] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v24d0 => {
                self.neon[24] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[24] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v24d1 => {
                self.neon[24] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[24] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v25d0 => {
                self.neon[25] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[25] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v25d1 => {
                self.neon[25] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[25] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v26d0 => {
                self.neon[26] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[26] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v26d1 => {
                self.neon[26] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[26] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v27d0 => {
                self.neon[27] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[27] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v27d1 => {
                self.neon[27] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[27] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v28d0 => {
                self.neon[28] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[28] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v28d1 => {
                self.neon[28] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[28] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v29d0 => {
                self.neon[29] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[29] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v29d1 => {
                self.neon[29] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[29] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v30d0 => {
                self.neon[30] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[30] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v30d1 => {
                self.neon[30] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[30] |= (value.get_quad() as u128) << (64 * 1);
            }
            Arm64Reg::v31d0 => {
                self.neon[31] &= 0xffffffffffffffff_u128 << (64 * 0);
                self.neon[31] |= (value.get_quad() as u128) << (64 * 0);
            }
            Arm64Reg::v31d1 => {
                self.neon[31] &= 0xffffffffffffffff_u128 << (64 * 1);
                self.neon[31] |= (value.get_quad() as u128) << (64 * 1);
            }
        };
    }
}

impl Arm64State {
    pub fn get(&self, reg: Arm64Reg) -> ILVal {
        match reg {
            Arm64Reg::w0 => ILVal::Word(self.gregs[0] as u32),
            Arm64Reg::w1 => ILVal::Word(self.gregs[1] as u32),
            Arm64Reg::w2 => ILVal::Word(self.gregs[2] as u32),
            Arm64Reg::w3 => ILVal::Word(self.gregs[3] as u32),
            Arm64Reg::w4 => ILVal::Word(self.gregs[4] as u32),
            Arm64Reg::w5 => ILVal::Word(self.gregs[5] as u32),
            Arm64Reg::w6 => ILVal::Word(self.gregs[6] as u32),
            Arm64Reg::w7 => ILVal::Word(self.gregs[7] as u32),
            Arm64Reg::w8 => ILVal::Word(self.gregs[8] as u32),
            Arm64Reg::w9 => ILVal::Word(self.gregs[9] as u32),
            Arm64Reg::w10 => ILVal::Word(self.gregs[10] as u32),
            Arm64Reg::w11 => ILVal::Word(self.gregs[11] as u32),
            Arm64Reg::w12 => ILVal::Word(self.gregs[12] as u32),
            Arm64Reg::w13 => ILVal::Word(self.gregs[13] as u32),
            Arm64Reg::w14 => ILVal::Word(self.gregs[14] as u32),
            Arm64Reg::w15 => ILVal::Word(self.gregs[15] as u32),
            Arm64Reg::w16 => ILVal::Word(self.gregs[16] as u32),
            Arm64Reg::w17 => ILVal::Word(self.gregs[17] as u32),
            Arm64Reg::w18 => ILVal::Word(self.gregs[18] as u32),
            Arm64Reg::w19 => ILVal::Word(self.gregs[19] as u32),
            Arm64Reg::w20 => ILVal::Word(self.gregs[20] as u32),
            Arm64Reg::w21 => ILVal::Word(self.gregs[21] as u32),
            Arm64Reg::w22 => ILVal::Word(self.gregs[22] as u32),
            Arm64Reg::w23 => ILVal::Word(self.gregs[23] as u32),
            Arm64Reg::w24 => ILVal::Word(self.gregs[24] as u32),
            Arm64Reg::w25 => ILVal::Word(self.gregs[25] as u32),
            Arm64Reg::w26 => ILVal::Word(self.gregs[26] as u32),
            Arm64Reg::w27 => ILVal::Word(self.gregs[27] as u32),
            Arm64Reg::w28 => ILVal::Word(self.gregs[28] as u32),
            Arm64Reg::w29 => ILVal::Word(self.gregs[29] as u32),
            Arm64Reg::w30 => ILVal::Word(self.gregs[30] as u32),
            Arm64Reg::wsp => ILVal::Word(self.gregs[31] as u32),
            Arm64Reg::x0 => ILVal::Quad(self.gregs[0]),
            Arm64Reg::x1 => ILVal::Quad(self.gregs[1]),
            Arm64Reg::x2 => ILVal::Quad(self.gregs[2]),
            Arm64Reg::x3 => ILVal::Quad(self.gregs[3]),
            Arm64Reg::x4 => ILVal::Quad(self.gregs[4]),
            Arm64Reg::x5 => ILVal::Quad(self.gregs[5]),
            Arm64Reg::x6 => ILVal::Quad(self.gregs[6]),
            Arm64Reg::x7 => ILVal::Quad(self.gregs[7]),
            Arm64Reg::x8 => ILVal::Quad(self.gregs[8]),
            Arm64Reg::x9 => ILVal::Quad(self.gregs[9]),
            Arm64Reg::x10 => ILVal::Quad(self.gregs[10]),
            Arm64Reg::x11 => ILVal::Quad(self.gregs[11]),
            Arm64Reg::x12 => ILVal::Quad(self.gregs[12]),
            Arm64Reg::x13 => ILVal::Quad(self.gregs[13]),
            Arm64Reg::x14 => ILVal::Quad(self.gregs[14]),
            Arm64Reg::x15 => ILVal::Quad(self.gregs[15]),
            Arm64Reg::x16 => ILVal::Quad(self.gregs[16]),
            Arm64Reg::x17 => ILVal::Quad(self.gregs[17]),
            Arm64Reg::x18 => ILVal::Quad(self.gregs[18]),
            Arm64Reg::x19 => ILVal::Quad(self.gregs[19]),
            Arm64Reg::x20 => ILVal::Quad(self.gregs[20]),
            Arm64Reg::x21 => ILVal::Quad(self.gregs[21]),
            Arm64Reg::x22 => ILVal::Quad(self.gregs[22]),
            Arm64Reg::x23 => ILVal::Quad(self.gregs[23]),
            Arm64Reg::x24 => ILVal::Quad(self.gregs[24]),
            Arm64Reg::x25 => ILVal::Quad(self.gregs[25]),
            Arm64Reg::x26 => ILVal::Quad(self.gregs[26]),
            Arm64Reg::x27 => ILVal::Quad(self.gregs[27]),
            Arm64Reg::x28 => ILVal::Quad(self.gregs[28]),
            Arm64Reg::fp => ILVal::Quad(self.gregs[29]),
            Arm64Reg::lr => ILVal::Quad(self.gregs[30]),
            Arm64Reg::sp => ILVal::Quad(self.gregs[31]),
            Arm64Reg::syscall_info => ILVal::Quad(self.syscall_info),
            Arm64Reg::d0 => ILVal::Quad(self.neon[0] as u64),
            Arm64Reg::d1 => ILVal::Quad(self.neon[1] as u64),
            Arm64Reg::d2 => ILVal::Quad(self.neon[2] as u64),
            Arm64Reg::d3 => ILVal::Quad(self.neon[3] as u64),
            Arm64Reg::d4 => ILVal::Quad(self.neon[4] as u64),
            Arm64Reg::d5 => ILVal::Quad(self.neon[5] as u64),
            Arm64Reg::d6 => ILVal::Quad(self.neon[6] as u64),
            Arm64Reg::d7 => ILVal::Quad(self.neon[7] as u64),
            Arm64Reg::d8 => ILVal::Quad(self.neon[8] as u64),
            Arm64Reg::d9 => ILVal::Quad(self.neon[9] as u64),
            Arm64Reg::d10 => ILVal::Quad(self.neon[10] as u64),
            Arm64Reg::d11 => ILVal::Quad(self.neon[11] as u64),
            Arm64Reg::d12 => ILVal::Quad(self.neon[12] as u64),
            Arm64Reg::d13 => ILVal::Quad(self.neon[13] as u64),
            Arm64Reg::d14 => ILVal::Quad(self.neon[14] as u64),
            Arm64Reg::d15 => ILVal::Quad(self.neon[15] as u64),
            Arm64Reg::d16 => ILVal::Quad(self.neon[16] as u64),
            Arm64Reg::d17 => ILVal::Quad(self.neon[17] as u64),
            Arm64Reg::d18 => ILVal::Quad(self.neon[18] as u64),
            Arm64Reg::d19 => ILVal::Quad(self.neon[19] as u64),
            Arm64Reg::d20 => ILVal::Quad(self.neon[20] as u64),
            Arm64Reg::d21 => ILVal::Quad(self.neon[21] as u64),
            Arm64Reg::d22 => ILVal::Quad(self.neon[22] as u64),
            Arm64Reg::d23 => ILVal::Quad(self.neon[23] as u64),
            Arm64Reg::d24 => ILVal::Quad(self.neon[24] as u64),
            Arm64Reg::d25 => ILVal::Quad(self.neon[25] as u64),
            Arm64Reg::d26 => ILVal::Quad(self.neon[26] as u64),
            Arm64Reg::d27 => ILVal::Quad(self.neon[27] as u64),
            Arm64Reg::d28 => ILVal::Quad(self.neon[28] as u64),
            Arm64Reg::d29 => ILVal::Quad(self.neon[29] as u64),
            Arm64Reg::d30 => ILVal::Quad(self.neon[30] as u64),
            Arm64Reg::d31 => ILVal::Quad(self.neon[31] as u64),
            Arm64Reg::s0 => ILVal::Word(self.neon[0] as u32),
            Arm64Reg::s1 => ILVal::Word((self.neon[0] >> 32) as u32),
            Arm64Reg::s2 => ILVal::Word(self.neon[1] as u32),
            Arm64Reg::s3 => ILVal::Word((self.neon[1] >> 32) as u32),
            Arm64Reg::s4 => ILVal::Word(self.neon[2] as u32),
            Arm64Reg::s5 => ILVal::Word((self.neon[2] >> 32) as u32),
            Arm64Reg::s6 => ILVal::Word(self.neon[3] as u32),
            Arm64Reg::s7 => ILVal::Word((self.neon[3] >> 32) as u32),
            Arm64Reg::s8 => ILVal::Word(self.neon[4] as u32),
            Arm64Reg::s9 => ILVal::Word((self.neon[4] >> 32) as u32),
            Arm64Reg::s10 => ILVal::Word(self.neon[5] as u32),
            Arm64Reg::s11 => ILVal::Word((self.neon[5] >> 32) as u32),
            Arm64Reg::s12 => ILVal::Word(self.neon[6] as u32),
            Arm64Reg::s13 => ILVal::Word((self.neon[6] >> 32) as u32),
            Arm64Reg::s14 => ILVal::Word(self.neon[7] as u32),
            Arm64Reg::s15 => ILVal::Word((self.neon[7] >> 32) as u32),
            Arm64Reg::s16 => ILVal::Word(self.neon[8] as u32),
            Arm64Reg::s17 => ILVal::Word((self.neon[8] >> 32) as u32),
            Arm64Reg::s18 => ILVal::Word(self.neon[9] as u32),
            Arm64Reg::s19 => ILVal::Word((self.neon[9] >> 32) as u32),
            Arm64Reg::s20 => ILVal::Word(self.neon[10] as u32),
            Arm64Reg::s21 => ILVal::Word((self.neon[10] >> 32) as u32),
            Arm64Reg::s22 => ILVal::Word(self.neon[11] as u32),
            Arm64Reg::s23 => ILVal::Word((self.neon[11] >> 32) as u32),
            Arm64Reg::s24 => ILVal::Word(self.neon[12] as u32),
            Arm64Reg::s25 => ILVal::Word((self.neon[12] >> 32) as u32),
            Arm64Reg::s26 => ILVal::Word(self.neon[13] as u32),
            Arm64Reg::s27 => ILVal::Word((self.neon[13] >> 32) as u32),
            Arm64Reg::s28 => ILVal::Word(self.neon[14] as u32),
            Arm64Reg::s29 => ILVal::Word((self.neon[14] >> 32) as u32),
            Arm64Reg::s30 => ILVal::Word(self.neon[15] as u32),
            Arm64Reg::s31 => ILVal::Word((self.neon[15] >> 32) as u32),
            Arm64Reg::q0 => ILVal::Big(Big::from(self.neon[0].to_le_bytes())),
            Arm64Reg::q1 => ILVal::Big(Big::from(self.neon[1].to_le_bytes())),
            Arm64Reg::q2 => ILVal::Big(Big::from(self.neon[2].to_le_bytes())),
            Arm64Reg::q3 => ILVal::Big(Big::from(self.neon[3].to_le_bytes())),
            Arm64Reg::q4 => ILVal::Big(Big::from(self.neon[4].to_le_bytes())),
            Arm64Reg::q5 => ILVal::Big(Big::from(self.neon[5].to_le_bytes())),
            Arm64Reg::q6 => ILVal::Big(Big::from(self.neon[6].to_le_bytes())),
            Arm64Reg::q7 => ILVal::Big(Big::from(self.neon[7].to_le_bytes())),
            Arm64Reg::q8 => ILVal::Big(Big::from(self.neon[8].to_le_bytes())),
            Arm64Reg::q9 => ILVal::Big(Big::from(self.neon[9].to_le_bytes())),
            Arm64Reg::q10 => ILVal::Big(Big::from(self.neon[10].to_le_bytes())),
            Arm64Reg::q11 => ILVal::Big(Big::from(self.neon[11].to_le_bytes())),
            Arm64Reg::q12 => ILVal::Big(Big::from(self.neon[12].to_le_bytes())),
            Arm64Reg::q13 => ILVal::Big(Big::from(self.neon[13].to_le_bytes())),
            Arm64Reg::q14 => ILVal::Big(Big::from(self.neon[14].to_le_bytes())),
            Arm64Reg::q15 => ILVal::Big(Big::from(self.neon[15].to_le_bytes())),
            Arm64Reg::q16 => ILVal::Big(Big::from(self.neon[16].to_le_bytes())),
            Arm64Reg::q17 => ILVal::Big(Big::from(self.neon[17].to_le_bytes())),
            Arm64Reg::q18 => ILVal::Big(Big::from(self.neon[18].to_le_bytes())),
            Arm64Reg::q19 => ILVal::Big(Big::from(self.neon[19].to_le_bytes())),
            Arm64Reg::q20 => ILVal::Big(Big::from(self.neon[20].to_le_bytes())),
            Arm64Reg::q21 => ILVal::Big(Big::from(self.neon[21].to_le_bytes())),
            Arm64Reg::q22 => ILVal::Big(Big::from(self.neon[22].to_le_bytes())),
            Arm64Reg::q23 => ILVal::Big(Big::from(self.neon[23].to_le_bytes())),
            Arm64Reg::q24 => ILVal::Big(Big::from(self.neon[24].to_le_bytes())),
            Arm64Reg::q25 => ILVal::Big(Big::from(self.neon[25].to_le_bytes())),
            Arm64Reg::q26 => ILVal::Big(Big::from(self.neon[26].to_le_bytes())),
            Arm64Reg::q27 => ILVal::Big(Big::from(self.neon[27].to_le_bytes())),
            Arm64Reg::q28 => ILVal::Big(Big::from(self.neon[28].to_le_bytes())),
            Arm64Reg::q29 => ILVal::Big(Big::from(self.neon[29].to_le_bytes())),
            Arm64Reg::q30 => ILVal::Big(Big::from(self.neon[30].to_le_bytes())),
            Arm64Reg::q31 => ILVal::Big(Big::from(self.neon[31].to_le_bytes())),
            Arm64Reg::v0b0 => ILVal::Byte(((self.neon[0] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v0b1 => ILVal::Byte(((self.neon[0] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v0b2 => ILVal::Byte(((self.neon[0] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v0b3 => ILVal::Byte(((self.neon[0] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v0b4 => ILVal::Byte(((self.neon[0] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v0b5 => ILVal::Byte(((self.neon[0] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v0b6 => ILVal::Byte(((self.neon[0] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v0b7 => ILVal::Byte(((self.neon[0] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v0b8 => ILVal::Byte(((self.neon[0] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v0b9 => ILVal::Byte(((self.neon[0] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v0b10 => ILVal::Byte(((self.neon[0] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v0b11 => ILVal::Byte(((self.neon[0] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v0b12 => ILVal::Byte(((self.neon[0] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v0b13 => ILVal::Byte(((self.neon[0] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v0b14 => ILVal::Byte(((self.neon[0] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v0b15 => ILVal::Byte(((self.neon[0] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v1b0 => ILVal::Byte(((self.neon[1] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v1b1 => ILVal::Byte(((self.neon[1] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v1b2 => ILVal::Byte(((self.neon[1] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v1b3 => ILVal::Byte(((self.neon[1] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v1b4 => ILVal::Byte(((self.neon[1] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v1b5 => ILVal::Byte(((self.neon[1] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v1b6 => ILVal::Byte(((self.neon[1] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v1b7 => ILVal::Byte(((self.neon[1] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v1b8 => ILVal::Byte(((self.neon[1] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v1b9 => ILVal::Byte(((self.neon[1] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v1b10 => ILVal::Byte(((self.neon[1] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v1b11 => ILVal::Byte(((self.neon[1] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v1b12 => ILVal::Byte(((self.neon[1] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v1b13 => ILVal::Byte(((self.neon[1] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v1b14 => ILVal::Byte(((self.neon[1] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v1b15 => ILVal::Byte(((self.neon[1] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v2b0 => ILVal::Byte(((self.neon[2] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v2b1 => ILVal::Byte(((self.neon[2] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v2b2 => ILVal::Byte(((self.neon[2] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v2b3 => ILVal::Byte(((self.neon[2] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v2b4 => ILVal::Byte(((self.neon[2] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v2b5 => ILVal::Byte(((self.neon[2] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v2b6 => ILVal::Byte(((self.neon[2] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v2b7 => ILVal::Byte(((self.neon[2] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v2b8 => ILVal::Byte(((self.neon[2] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v2b9 => ILVal::Byte(((self.neon[2] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v2b10 => ILVal::Byte(((self.neon[2] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v2b11 => ILVal::Byte(((self.neon[2] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v2b12 => ILVal::Byte(((self.neon[2] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v2b13 => ILVal::Byte(((self.neon[2] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v2b14 => ILVal::Byte(((self.neon[2] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v2b15 => ILVal::Byte(((self.neon[2] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v3b0 => ILVal::Byte(((self.neon[3] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v3b1 => ILVal::Byte(((self.neon[3] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v3b2 => ILVal::Byte(((self.neon[3] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v3b3 => ILVal::Byte(((self.neon[3] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v3b4 => ILVal::Byte(((self.neon[3] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v3b5 => ILVal::Byte(((self.neon[3] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v3b6 => ILVal::Byte(((self.neon[3] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v3b7 => ILVal::Byte(((self.neon[3] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v3b8 => ILVal::Byte(((self.neon[3] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v3b9 => ILVal::Byte(((self.neon[3] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v3b10 => ILVal::Byte(((self.neon[3] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v3b11 => ILVal::Byte(((self.neon[3] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v3b12 => ILVal::Byte(((self.neon[3] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v3b13 => ILVal::Byte(((self.neon[3] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v3b14 => ILVal::Byte(((self.neon[3] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v3b15 => ILVal::Byte(((self.neon[3] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v4b0 => ILVal::Byte(((self.neon[4] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v4b1 => ILVal::Byte(((self.neon[4] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v4b2 => ILVal::Byte(((self.neon[4] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v4b3 => ILVal::Byte(((self.neon[4] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v4b4 => ILVal::Byte(((self.neon[4] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v4b5 => ILVal::Byte(((self.neon[4] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v4b6 => ILVal::Byte(((self.neon[4] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v4b7 => ILVal::Byte(((self.neon[4] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v4b8 => ILVal::Byte(((self.neon[4] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v4b9 => ILVal::Byte(((self.neon[4] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v4b10 => ILVal::Byte(((self.neon[4] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v4b11 => ILVal::Byte(((self.neon[4] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v4b12 => ILVal::Byte(((self.neon[4] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v4b13 => ILVal::Byte(((self.neon[4] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v4b14 => ILVal::Byte(((self.neon[4] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v4b15 => ILVal::Byte(((self.neon[4] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v5b0 => ILVal::Byte(((self.neon[5] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v5b1 => ILVal::Byte(((self.neon[5] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v5b2 => ILVal::Byte(((self.neon[5] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v5b3 => ILVal::Byte(((self.neon[5] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v5b4 => ILVal::Byte(((self.neon[5] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v5b5 => ILVal::Byte(((self.neon[5] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v5b6 => ILVal::Byte(((self.neon[5] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v5b7 => ILVal::Byte(((self.neon[5] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v5b8 => ILVal::Byte(((self.neon[5] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v5b9 => ILVal::Byte(((self.neon[5] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v5b10 => ILVal::Byte(((self.neon[5] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v5b11 => ILVal::Byte(((self.neon[5] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v5b12 => ILVal::Byte(((self.neon[5] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v5b13 => ILVal::Byte(((self.neon[5] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v5b14 => ILVal::Byte(((self.neon[5] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v5b15 => ILVal::Byte(((self.neon[5] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v6b0 => ILVal::Byte(((self.neon[6] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v6b1 => ILVal::Byte(((self.neon[6] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v6b2 => ILVal::Byte(((self.neon[6] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v6b3 => ILVal::Byte(((self.neon[6] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v6b4 => ILVal::Byte(((self.neon[6] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v6b5 => ILVal::Byte(((self.neon[6] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v6b6 => ILVal::Byte(((self.neon[6] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v6b7 => ILVal::Byte(((self.neon[6] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v6b8 => ILVal::Byte(((self.neon[6] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v6b9 => ILVal::Byte(((self.neon[6] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v6b10 => ILVal::Byte(((self.neon[6] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v6b11 => ILVal::Byte(((self.neon[6] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v6b12 => ILVal::Byte(((self.neon[6] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v6b13 => ILVal::Byte(((self.neon[6] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v6b14 => ILVal::Byte(((self.neon[6] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v6b15 => ILVal::Byte(((self.neon[6] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v7b0 => ILVal::Byte(((self.neon[7] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v7b1 => ILVal::Byte(((self.neon[7] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v7b2 => ILVal::Byte(((self.neon[7] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v7b3 => ILVal::Byte(((self.neon[7] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v7b4 => ILVal::Byte(((self.neon[7] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v7b5 => ILVal::Byte(((self.neon[7] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v7b6 => ILVal::Byte(((self.neon[7] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v7b7 => ILVal::Byte(((self.neon[7] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v7b8 => ILVal::Byte(((self.neon[7] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v7b9 => ILVal::Byte(((self.neon[7] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v7b10 => ILVal::Byte(((self.neon[7] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v7b11 => ILVal::Byte(((self.neon[7] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v7b12 => ILVal::Byte(((self.neon[7] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v7b13 => ILVal::Byte(((self.neon[7] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v7b14 => ILVal::Byte(((self.neon[7] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v7b15 => ILVal::Byte(((self.neon[7] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v8b0 => ILVal::Byte(((self.neon[8] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v8b1 => ILVal::Byte(((self.neon[8] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v8b2 => ILVal::Byte(((self.neon[8] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v8b3 => ILVal::Byte(((self.neon[8] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v8b4 => ILVal::Byte(((self.neon[8] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v8b5 => ILVal::Byte(((self.neon[8] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v8b6 => ILVal::Byte(((self.neon[8] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v8b7 => ILVal::Byte(((self.neon[8] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v8b8 => ILVal::Byte(((self.neon[8] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v8b9 => ILVal::Byte(((self.neon[8] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v8b10 => ILVal::Byte(((self.neon[8] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v8b11 => ILVal::Byte(((self.neon[8] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v8b12 => ILVal::Byte(((self.neon[8] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v8b13 => ILVal::Byte(((self.neon[8] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v8b14 => ILVal::Byte(((self.neon[8] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v8b15 => ILVal::Byte(((self.neon[8] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v9b0 => ILVal::Byte(((self.neon[9] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v9b1 => ILVal::Byte(((self.neon[9] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v9b2 => ILVal::Byte(((self.neon[9] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v9b3 => ILVal::Byte(((self.neon[9] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v9b4 => ILVal::Byte(((self.neon[9] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v9b5 => ILVal::Byte(((self.neon[9] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v9b6 => ILVal::Byte(((self.neon[9] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v9b7 => ILVal::Byte(((self.neon[9] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v9b8 => ILVal::Byte(((self.neon[9] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v9b9 => ILVal::Byte(((self.neon[9] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v9b10 => ILVal::Byte(((self.neon[9] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v9b11 => ILVal::Byte(((self.neon[9] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v9b12 => ILVal::Byte(((self.neon[9] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v9b13 => ILVal::Byte(((self.neon[9] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v9b14 => ILVal::Byte(((self.neon[9] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v9b15 => ILVal::Byte(((self.neon[9] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v10b0 => ILVal::Byte(((self.neon[10] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v10b1 => ILVal::Byte(((self.neon[10] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v10b2 => ILVal::Byte(((self.neon[10] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v10b3 => ILVal::Byte(((self.neon[10] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v10b4 => ILVal::Byte(((self.neon[10] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v10b5 => ILVal::Byte(((self.neon[10] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v10b6 => ILVal::Byte(((self.neon[10] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v10b7 => ILVal::Byte(((self.neon[10] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v10b8 => ILVal::Byte(((self.neon[10] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v10b9 => ILVal::Byte(((self.neon[10] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v10b10 => ILVal::Byte(((self.neon[10] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v10b11 => ILVal::Byte(((self.neon[10] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v10b12 => ILVal::Byte(((self.neon[10] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v10b13 => ILVal::Byte(((self.neon[10] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v10b14 => ILVal::Byte(((self.neon[10] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v10b15 => ILVal::Byte(((self.neon[10] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v11b0 => ILVal::Byte(((self.neon[11] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v11b1 => ILVal::Byte(((self.neon[11] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v11b2 => ILVal::Byte(((self.neon[11] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v11b3 => ILVal::Byte(((self.neon[11] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v11b4 => ILVal::Byte(((self.neon[11] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v11b5 => ILVal::Byte(((self.neon[11] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v11b6 => ILVal::Byte(((self.neon[11] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v11b7 => ILVal::Byte(((self.neon[11] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v11b8 => ILVal::Byte(((self.neon[11] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v11b9 => ILVal::Byte(((self.neon[11] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v11b10 => ILVal::Byte(((self.neon[11] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v11b11 => ILVal::Byte(((self.neon[11] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v11b12 => ILVal::Byte(((self.neon[11] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v11b13 => ILVal::Byte(((self.neon[11] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v11b14 => ILVal::Byte(((self.neon[11] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v11b15 => ILVal::Byte(((self.neon[11] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v12b0 => ILVal::Byte(((self.neon[12] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v12b1 => ILVal::Byte(((self.neon[12] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v12b2 => ILVal::Byte(((self.neon[12] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v12b3 => ILVal::Byte(((self.neon[12] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v12b4 => ILVal::Byte(((self.neon[12] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v12b5 => ILVal::Byte(((self.neon[12] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v12b6 => ILVal::Byte(((self.neon[12] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v12b7 => ILVal::Byte(((self.neon[12] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v12b8 => ILVal::Byte(((self.neon[12] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v12b9 => ILVal::Byte(((self.neon[12] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v12b10 => ILVal::Byte(((self.neon[12] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v12b11 => ILVal::Byte(((self.neon[12] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v12b12 => ILVal::Byte(((self.neon[12] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v12b13 => ILVal::Byte(((self.neon[12] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v12b14 => ILVal::Byte(((self.neon[12] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v12b15 => ILVal::Byte(((self.neon[12] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v13b0 => ILVal::Byte(((self.neon[13] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v13b1 => ILVal::Byte(((self.neon[13] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v13b2 => ILVal::Byte(((self.neon[13] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v13b3 => ILVal::Byte(((self.neon[13] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v13b4 => ILVal::Byte(((self.neon[13] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v13b5 => ILVal::Byte(((self.neon[13] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v13b6 => ILVal::Byte(((self.neon[13] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v13b7 => ILVal::Byte(((self.neon[13] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v13b8 => ILVal::Byte(((self.neon[13] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v13b9 => ILVal::Byte(((self.neon[13] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v13b10 => ILVal::Byte(((self.neon[13] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v13b11 => ILVal::Byte(((self.neon[13] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v13b12 => ILVal::Byte(((self.neon[13] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v13b13 => ILVal::Byte(((self.neon[13] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v13b14 => ILVal::Byte(((self.neon[13] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v13b15 => ILVal::Byte(((self.neon[13] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v14b0 => ILVal::Byte(((self.neon[14] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v14b1 => ILVal::Byte(((self.neon[14] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v14b2 => ILVal::Byte(((self.neon[14] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v14b3 => ILVal::Byte(((self.neon[14] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v14b4 => ILVal::Byte(((self.neon[14] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v14b5 => ILVal::Byte(((self.neon[14] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v14b6 => ILVal::Byte(((self.neon[14] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v14b7 => ILVal::Byte(((self.neon[14] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v14b8 => ILVal::Byte(((self.neon[14] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v14b9 => ILVal::Byte(((self.neon[14] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v14b10 => ILVal::Byte(((self.neon[14] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v14b11 => ILVal::Byte(((self.neon[14] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v14b12 => ILVal::Byte(((self.neon[14] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v14b13 => ILVal::Byte(((self.neon[14] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v14b14 => ILVal::Byte(((self.neon[14] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v14b15 => ILVal::Byte(((self.neon[14] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v15b0 => ILVal::Byte(((self.neon[15] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v15b1 => ILVal::Byte(((self.neon[15] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v15b2 => ILVal::Byte(((self.neon[15] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v15b3 => ILVal::Byte(((self.neon[15] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v15b4 => ILVal::Byte(((self.neon[15] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v15b5 => ILVal::Byte(((self.neon[15] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v15b6 => ILVal::Byte(((self.neon[15] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v15b7 => ILVal::Byte(((self.neon[15] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v15b8 => ILVal::Byte(((self.neon[15] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v15b9 => ILVal::Byte(((self.neon[15] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v15b10 => ILVal::Byte(((self.neon[15] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v15b11 => ILVal::Byte(((self.neon[15] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v15b12 => ILVal::Byte(((self.neon[15] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v15b13 => ILVal::Byte(((self.neon[15] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v15b14 => ILVal::Byte(((self.neon[15] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v15b15 => ILVal::Byte(((self.neon[15] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v16b0 => ILVal::Byte(((self.neon[16] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v16b1 => ILVal::Byte(((self.neon[16] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v16b2 => ILVal::Byte(((self.neon[16] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v16b3 => ILVal::Byte(((self.neon[16] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v16b4 => ILVal::Byte(((self.neon[16] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v16b5 => ILVal::Byte(((self.neon[16] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v16b6 => ILVal::Byte(((self.neon[16] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v16b7 => ILVal::Byte(((self.neon[16] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v16b8 => ILVal::Byte(((self.neon[16] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v16b9 => ILVal::Byte(((self.neon[16] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v16b10 => ILVal::Byte(((self.neon[16] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v16b11 => ILVal::Byte(((self.neon[16] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v16b12 => ILVal::Byte(((self.neon[16] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v16b13 => ILVal::Byte(((self.neon[16] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v16b14 => ILVal::Byte(((self.neon[16] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v16b15 => ILVal::Byte(((self.neon[16] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v17b0 => ILVal::Byte(((self.neon[17] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v17b1 => ILVal::Byte(((self.neon[17] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v17b2 => ILVal::Byte(((self.neon[17] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v17b3 => ILVal::Byte(((self.neon[17] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v17b4 => ILVal::Byte(((self.neon[17] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v17b5 => ILVal::Byte(((self.neon[17] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v17b6 => ILVal::Byte(((self.neon[17] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v17b7 => ILVal::Byte(((self.neon[17] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v17b8 => ILVal::Byte(((self.neon[17] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v17b9 => ILVal::Byte(((self.neon[17] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v17b10 => ILVal::Byte(((self.neon[17] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v17b11 => ILVal::Byte(((self.neon[17] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v17b12 => ILVal::Byte(((self.neon[17] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v17b13 => ILVal::Byte(((self.neon[17] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v17b14 => ILVal::Byte(((self.neon[17] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v17b15 => ILVal::Byte(((self.neon[17] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v18b0 => ILVal::Byte(((self.neon[18] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v18b1 => ILVal::Byte(((self.neon[18] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v18b2 => ILVal::Byte(((self.neon[18] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v18b3 => ILVal::Byte(((self.neon[18] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v18b4 => ILVal::Byte(((self.neon[18] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v18b5 => ILVal::Byte(((self.neon[18] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v18b6 => ILVal::Byte(((self.neon[18] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v18b7 => ILVal::Byte(((self.neon[18] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v18b8 => ILVal::Byte(((self.neon[18] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v18b9 => ILVal::Byte(((self.neon[18] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v18b10 => ILVal::Byte(((self.neon[18] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v18b11 => ILVal::Byte(((self.neon[18] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v18b12 => ILVal::Byte(((self.neon[18] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v18b13 => ILVal::Byte(((self.neon[18] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v18b14 => ILVal::Byte(((self.neon[18] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v18b15 => ILVal::Byte(((self.neon[18] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v19b0 => ILVal::Byte(((self.neon[19] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v19b1 => ILVal::Byte(((self.neon[19] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v19b2 => ILVal::Byte(((self.neon[19] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v19b3 => ILVal::Byte(((self.neon[19] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v19b4 => ILVal::Byte(((self.neon[19] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v19b5 => ILVal::Byte(((self.neon[19] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v19b6 => ILVal::Byte(((self.neon[19] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v19b7 => ILVal::Byte(((self.neon[19] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v19b8 => ILVal::Byte(((self.neon[19] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v19b9 => ILVal::Byte(((self.neon[19] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v19b10 => ILVal::Byte(((self.neon[19] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v19b11 => ILVal::Byte(((self.neon[19] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v19b12 => ILVal::Byte(((self.neon[19] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v19b13 => ILVal::Byte(((self.neon[19] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v19b14 => ILVal::Byte(((self.neon[19] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v19b15 => ILVal::Byte(((self.neon[19] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v20b0 => ILVal::Byte(((self.neon[20] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v20b1 => ILVal::Byte(((self.neon[20] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v20b2 => ILVal::Byte(((self.neon[20] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v20b3 => ILVal::Byte(((self.neon[20] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v20b4 => ILVal::Byte(((self.neon[20] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v20b5 => ILVal::Byte(((self.neon[20] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v20b6 => ILVal::Byte(((self.neon[20] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v20b7 => ILVal::Byte(((self.neon[20] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v20b8 => ILVal::Byte(((self.neon[20] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v20b9 => ILVal::Byte(((self.neon[20] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v20b10 => ILVal::Byte(((self.neon[20] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v20b11 => ILVal::Byte(((self.neon[20] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v20b12 => ILVal::Byte(((self.neon[20] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v20b13 => ILVal::Byte(((self.neon[20] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v20b14 => ILVal::Byte(((self.neon[20] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v20b15 => ILVal::Byte(((self.neon[20] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v21b0 => ILVal::Byte(((self.neon[21] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v21b1 => ILVal::Byte(((self.neon[21] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v21b2 => ILVal::Byte(((self.neon[21] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v21b3 => ILVal::Byte(((self.neon[21] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v21b4 => ILVal::Byte(((self.neon[21] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v21b5 => ILVal::Byte(((self.neon[21] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v21b6 => ILVal::Byte(((self.neon[21] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v21b7 => ILVal::Byte(((self.neon[21] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v21b8 => ILVal::Byte(((self.neon[21] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v21b9 => ILVal::Byte(((self.neon[21] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v21b10 => ILVal::Byte(((self.neon[21] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v21b11 => ILVal::Byte(((self.neon[21] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v21b12 => ILVal::Byte(((self.neon[21] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v21b13 => ILVal::Byte(((self.neon[21] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v21b14 => ILVal::Byte(((self.neon[21] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v21b15 => ILVal::Byte(((self.neon[21] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v22b0 => ILVal::Byte(((self.neon[22] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v22b1 => ILVal::Byte(((self.neon[22] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v22b2 => ILVal::Byte(((self.neon[22] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v22b3 => ILVal::Byte(((self.neon[22] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v22b4 => ILVal::Byte(((self.neon[22] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v22b5 => ILVal::Byte(((self.neon[22] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v22b6 => ILVal::Byte(((self.neon[22] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v22b7 => ILVal::Byte(((self.neon[22] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v22b8 => ILVal::Byte(((self.neon[22] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v22b9 => ILVal::Byte(((self.neon[22] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v22b10 => ILVal::Byte(((self.neon[22] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v22b11 => ILVal::Byte(((self.neon[22] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v22b12 => ILVal::Byte(((self.neon[22] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v22b13 => ILVal::Byte(((self.neon[22] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v22b14 => ILVal::Byte(((self.neon[22] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v22b15 => ILVal::Byte(((self.neon[22] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v23b0 => ILVal::Byte(((self.neon[23] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v23b1 => ILVal::Byte(((self.neon[23] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v23b2 => ILVal::Byte(((self.neon[23] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v23b3 => ILVal::Byte(((self.neon[23] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v23b4 => ILVal::Byte(((self.neon[23] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v23b5 => ILVal::Byte(((self.neon[23] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v23b6 => ILVal::Byte(((self.neon[23] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v23b7 => ILVal::Byte(((self.neon[23] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v23b8 => ILVal::Byte(((self.neon[23] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v23b9 => ILVal::Byte(((self.neon[23] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v23b10 => ILVal::Byte(((self.neon[23] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v23b11 => ILVal::Byte(((self.neon[23] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v23b12 => ILVal::Byte(((self.neon[23] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v23b13 => ILVal::Byte(((self.neon[23] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v23b14 => ILVal::Byte(((self.neon[23] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v23b15 => ILVal::Byte(((self.neon[23] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v24b0 => ILVal::Byte(((self.neon[24] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v24b1 => ILVal::Byte(((self.neon[24] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v24b2 => ILVal::Byte(((self.neon[24] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v24b3 => ILVal::Byte(((self.neon[24] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v24b4 => ILVal::Byte(((self.neon[24] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v24b5 => ILVal::Byte(((self.neon[24] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v24b6 => ILVal::Byte(((self.neon[24] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v24b7 => ILVal::Byte(((self.neon[24] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v24b8 => ILVal::Byte(((self.neon[24] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v24b9 => ILVal::Byte(((self.neon[24] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v24b10 => ILVal::Byte(((self.neon[24] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v24b11 => ILVal::Byte(((self.neon[24] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v24b12 => ILVal::Byte(((self.neon[24] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v24b13 => ILVal::Byte(((self.neon[24] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v24b14 => ILVal::Byte(((self.neon[24] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v24b15 => ILVal::Byte(((self.neon[24] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v25b0 => ILVal::Byte(((self.neon[25] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v25b1 => ILVal::Byte(((self.neon[25] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v25b2 => ILVal::Byte(((self.neon[25] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v25b3 => ILVal::Byte(((self.neon[25] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v25b4 => ILVal::Byte(((self.neon[25] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v25b5 => ILVal::Byte(((self.neon[25] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v25b6 => ILVal::Byte(((self.neon[25] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v25b7 => ILVal::Byte(((self.neon[25] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v25b8 => ILVal::Byte(((self.neon[25] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v25b9 => ILVal::Byte(((self.neon[25] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v25b10 => ILVal::Byte(((self.neon[25] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v25b11 => ILVal::Byte(((self.neon[25] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v25b12 => ILVal::Byte(((self.neon[25] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v25b13 => ILVal::Byte(((self.neon[25] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v25b14 => ILVal::Byte(((self.neon[25] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v25b15 => ILVal::Byte(((self.neon[25] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v26b0 => ILVal::Byte(((self.neon[26] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v26b1 => ILVal::Byte(((self.neon[26] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v26b2 => ILVal::Byte(((self.neon[26] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v26b3 => ILVal::Byte(((self.neon[26] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v26b4 => ILVal::Byte(((self.neon[26] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v26b5 => ILVal::Byte(((self.neon[26] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v26b6 => ILVal::Byte(((self.neon[26] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v26b7 => ILVal::Byte(((self.neon[26] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v26b8 => ILVal::Byte(((self.neon[26] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v26b9 => ILVal::Byte(((self.neon[26] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v26b10 => ILVal::Byte(((self.neon[26] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v26b11 => ILVal::Byte(((self.neon[26] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v26b12 => ILVal::Byte(((self.neon[26] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v26b13 => ILVal::Byte(((self.neon[26] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v26b14 => ILVal::Byte(((self.neon[26] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v26b15 => ILVal::Byte(((self.neon[26] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v27b0 => ILVal::Byte(((self.neon[27] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v27b1 => ILVal::Byte(((self.neon[27] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v27b2 => ILVal::Byte(((self.neon[27] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v27b3 => ILVal::Byte(((self.neon[27] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v27b4 => ILVal::Byte(((self.neon[27] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v27b5 => ILVal::Byte(((self.neon[27] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v27b6 => ILVal::Byte(((self.neon[27] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v27b7 => ILVal::Byte(((self.neon[27] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v27b8 => ILVal::Byte(((self.neon[27] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v27b9 => ILVal::Byte(((self.neon[27] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v27b10 => ILVal::Byte(((self.neon[27] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v27b11 => ILVal::Byte(((self.neon[27] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v27b12 => ILVal::Byte(((self.neon[27] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v27b13 => ILVal::Byte(((self.neon[27] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v27b14 => ILVal::Byte(((self.neon[27] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v27b15 => ILVal::Byte(((self.neon[27] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v28b0 => ILVal::Byte(((self.neon[28] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v28b1 => ILVal::Byte(((self.neon[28] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v28b2 => ILVal::Byte(((self.neon[28] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v28b3 => ILVal::Byte(((self.neon[28] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v28b4 => ILVal::Byte(((self.neon[28] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v28b5 => ILVal::Byte(((self.neon[28] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v28b6 => ILVal::Byte(((self.neon[28] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v28b7 => ILVal::Byte(((self.neon[28] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v28b8 => ILVal::Byte(((self.neon[28] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v28b9 => ILVal::Byte(((self.neon[28] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v28b10 => ILVal::Byte(((self.neon[28] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v28b11 => ILVal::Byte(((self.neon[28] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v28b12 => ILVal::Byte(((self.neon[28] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v28b13 => ILVal::Byte(((self.neon[28] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v28b14 => ILVal::Byte(((self.neon[28] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v28b15 => ILVal::Byte(((self.neon[28] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v29b0 => ILVal::Byte(((self.neon[29] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v29b1 => ILVal::Byte(((self.neon[29] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v29b2 => ILVal::Byte(((self.neon[29] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v29b3 => ILVal::Byte(((self.neon[29] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v29b4 => ILVal::Byte(((self.neon[29] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v29b5 => ILVal::Byte(((self.neon[29] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v29b6 => ILVal::Byte(((self.neon[29] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v29b7 => ILVal::Byte(((self.neon[29] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v29b8 => ILVal::Byte(((self.neon[29] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v29b9 => ILVal::Byte(((self.neon[29] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v29b10 => ILVal::Byte(((self.neon[29] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v29b11 => ILVal::Byte(((self.neon[29] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v29b12 => ILVal::Byte(((self.neon[29] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v29b13 => ILVal::Byte(((self.neon[29] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v29b14 => ILVal::Byte(((self.neon[29] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v29b15 => ILVal::Byte(((self.neon[29] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v30b0 => ILVal::Byte(((self.neon[30] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v30b1 => ILVal::Byte(((self.neon[30] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v30b2 => ILVal::Byte(((self.neon[30] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v30b3 => ILVal::Byte(((self.neon[30] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v30b4 => ILVal::Byte(((self.neon[30] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v30b5 => ILVal::Byte(((self.neon[30] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v30b6 => ILVal::Byte(((self.neon[30] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v30b7 => ILVal::Byte(((self.neon[30] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v30b8 => ILVal::Byte(((self.neon[30] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v30b9 => ILVal::Byte(((self.neon[30] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v30b10 => ILVal::Byte(((self.neon[30] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v30b11 => ILVal::Byte(((self.neon[30] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v30b12 => ILVal::Byte(((self.neon[30] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v30b13 => ILVal::Byte(((self.neon[30] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v30b14 => ILVal::Byte(((self.neon[30] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v30b15 => ILVal::Byte(((self.neon[30] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v31b0 => ILVal::Byte(((self.neon[31] >> (0 * 8)) & 0xff) as u8),
            Arm64Reg::v31b1 => ILVal::Byte(((self.neon[31] >> (1 * 8)) & 0xff) as u8),
            Arm64Reg::v31b2 => ILVal::Byte(((self.neon[31] >> (2 * 8)) & 0xff) as u8),
            Arm64Reg::v31b3 => ILVal::Byte(((self.neon[31] >> (3 * 8)) & 0xff) as u8),
            Arm64Reg::v31b4 => ILVal::Byte(((self.neon[31] >> (4 * 8)) & 0xff) as u8),
            Arm64Reg::v31b5 => ILVal::Byte(((self.neon[31] >> (5 * 8)) & 0xff) as u8),
            Arm64Reg::v31b6 => ILVal::Byte(((self.neon[31] >> (6 * 8)) & 0xff) as u8),
            Arm64Reg::v31b7 => ILVal::Byte(((self.neon[31] >> (7 * 8)) & 0xff) as u8),
            Arm64Reg::v31b8 => ILVal::Byte(((self.neon[31] >> (8 * 8)) & 0xff) as u8),
            Arm64Reg::v31b9 => ILVal::Byte(((self.neon[31] >> (9 * 8)) & 0xff) as u8),
            Arm64Reg::v31b10 => ILVal::Byte(((self.neon[31] >> (10 * 8)) & 0xff) as u8),
            Arm64Reg::v31b11 => ILVal::Byte(((self.neon[31] >> (11 * 8)) & 0xff) as u8),
            Arm64Reg::v31b12 => ILVal::Byte(((self.neon[31] >> (12 * 8)) & 0xff) as u8),
            Arm64Reg::v31b13 => ILVal::Byte(((self.neon[31] >> (13 * 8)) & 0xff) as u8),
            Arm64Reg::v31b14 => ILVal::Byte(((self.neon[31] >> (14 * 8)) & 0xff) as u8),
            Arm64Reg::v31b15 => ILVal::Byte(((self.neon[31] >> (15 * 8)) & 0xff) as u8),
            Arm64Reg::v0h0 => ILVal::Short(((self.neon[0] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v0h1 => ILVal::Short(((self.neon[0] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v0h2 => ILVal::Short(((self.neon[0] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v0h3 => ILVal::Short(((self.neon[0] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v0h4 => ILVal::Short(((self.neon[0] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v0h5 => ILVal::Short(((self.neon[0] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v0h6 => ILVal::Short(((self.neon[0] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v0h7 => ILVal::Short(((self.neon[0] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v1h0 => ILVal::Short(((self.neon[1] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v1h1 => ILVal::Short(((self.neon[1] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v1h2 => ILVal::Short(((self.neon[1] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v1h3 => ILVal::Short(((self.neon[1] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v1h4 => ILVal::Short(((self.neon[1] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v1h5 => ILVal::Short(((self.neon[1] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v1h6 => ILVal::Short(((self.neon[1] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v1h7 => ILVal::Short(((self.neon[1] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v2h0 => ILVal::Short(((self.neon[2] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v2h1 => ILVal::Short(((self.neon[2] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v2h2 => ILVal::Short(((self.neon[2] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v2h3 => ILVal::Short(((self.neon[2] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v2h4 => ILVal::Short(((self.neon[2] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v2h5 => ILVal::Short(((self.neon[2] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v2h6 => ILVal::Short(((self.neon[2] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v2h7 => ILVal::Short(((self.neon[2] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v3h0 => ILVal::Short(((self.neon[3] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v3h1 => ILVal::Short(((self.neon[3] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v3h2 => ILVal::Short(((self.neon[3] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v3h3 => ILVal::Short(((self.neon[3] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v3h4 => ILVal::Short(((self.neon[3] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v3h5 => ILVal::Short(((self.neon[3] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v3h6 => ILVal::Short(((self.neon[3] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v3h7 => ILVal::Short(((self.neon[3] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v4h0 => ILVal::Short(((self.neon[4] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v4h1 => ILVal::Short(((self.neon[4] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v4h2 => ILVal::Short(((self.neon[4] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v4h3 => ILVal::Short(((self.neon[4] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v4h4 => ILVal::Short(((self.neon[4] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v4h5 => ILVal::Short(((self.neon[4] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v4h6 => ILVal::Short(((self.neon[4] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v4h7 => ILVal::Short(((self.neon[4] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v5h0 => ILVal::Short(((self.neon[5] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v5h1 => ILVal::Short(((self.neon[5] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v5h2 => ILVal::Short(((self.neon[5] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v5h3 => ILVal::Short(((self.neon[5] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v5h4 => ILVal::Short(((self.neon[5] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v5h5 => ILVal::Short(((self.neon[5] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v5h6 => ILVal::Short(((self.neon[5] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v5h7 => ILVal::Short(((self.neon[5] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v6h0 => ILVal::Short(((self.neon[6] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v6h1 => ILVal::Short(((self.neon[6] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v6h2 => ILVal::Short(((self.neon[6] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v6h3 => ILVal::Short(((self.neon[6] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v6h4 => ILVal::Short(((self.neon[6] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v6h5 => ILVal::Short(((self.neon[6] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v6h6 => ILVal::Short(((self.neon[6] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v6h7 => ILVal::Short(((self.neon[6] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v7h0 => ILVal::Short(((self.neon[7] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v7h1 => ILVal::Short(((self.neon[7] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v7h2 => ILVal::Short(((self.neon[7] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v7h3 => ILVal::Short(((self.neon[7] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v7h4 => ILVal::Short(((self.neon[7] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v7h5 => ILVal::Short(((self.neon[7] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v7h6 => ILVal::Short(((self.neon[7] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v7h7 => ILVal::Short(((self.neon[7] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v8h0 => ILVal::Short(((self.neon[8] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v8h1 => ILVal::Short(((self.neon[8] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v8h2 => ILVal::Short(((self.neon[8] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v8h3 => ILVal::Short(((self.neon[8] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v8h4 => ILVal::Short(((self.neon[8] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v8h5 => ILVal::Short(((self.neon[8] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v8h6 => ILVal::Short(((self.neon[8] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v8h7 => ILVal::Short(((self.neon[8] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v9h0 => ILVal::Short(((self.neon[9] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v9h1 => ILVal::Short(((self.neon[9] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v9h2 => ILVal::Short(((self.neon[9] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v9h3 => ILVal::Short(((self.neon[9] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v9h4 => ILVal::Short(((self.neon[9] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v9h5 => ILVal::Short(((self.neon[9] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v9h6 => ILVal::Short(((self.neon[9] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v9h7 => ILVal::Short(((self.neon[9] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v10h0 => ILVal::Short(((self.neon[10] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v10h1 => ILVal::Short(((self.neon[10] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v10h2 => ILVal::Short(((self.neon[10] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v10h3 => ILVal::Short(((self.neon[10] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v10h4 => ILVal::Short(((self.neon[10] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v10h5 => ILVal::Short(((self.neon[10] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v10h6 => ILVal::Short(((self.neon[10] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v10h7 => ILVal::Short(((self.neon[10] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v11h0 => ILVal::Short(((self.neon[11] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v11h1 => ILVal::Short(((self.neon[11] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v11h2 => ILVal::Short(((self.neon[11] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v11h3 => ILVal::Short(((self.neon[11] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v11h4 => ILVal::Short(((self.neon[11] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v11h5 => ILVal::Short(((self.neon[11] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v11h6 => ILVal::Short(((self.neon[11] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v11h7 => ILVal::Short(((self.neon[11] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v12h0 => ILVal::Short(((self.neon[12] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v12h1 => ILVal::Short(((self.neon[12] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v12h2 => ILVal::Short(((self.neon[12] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v12h3 => ILVal::Short(((self.neon[12] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v12h4 => ILVal::Short(((self.neon[12] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v12h5 => ILVal::Short(((self.neon[12] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v12h6 => ILVal::Short(((self.neon[12] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v12h7 => ILVal::Short(((self.neon[12] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v13h0 => ILVal::Short(((self.neon[13] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v13h1 => ILVal::Short(((self.neon[13] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v13h2 => ILVal::Short(((self.neon[13] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v13h3 => ILVal::Short(((self.neon[13] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v13h4 => ILVal::Short(((self.neon[13] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v13h5 => ILVal::Short(((self.neon[13] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v13h6 => ILVal::Short(((self.neon[13] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v13h7 => ILVal::Short(((self.neon[13] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v14h0 => ILVal::Short(((self.neon[14] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v14h1 => ILVal::Short(((self.neon[14] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v14h2 => ILVal::Short(((self.neon[14] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v14h3 => ILVal::Short(((self.neon[14] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v14h4 => ILVal::Short(((self.neon[14] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v14h5 => ILVal::Short(((self.neon[14] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v14h6 => ILVal::Short(((self.neon[14] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v14h7 => ILVal::Short(((self.neon[14] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v15h0 => ILVal::Short(((self.neon[15] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v15h1 => ILVal::Short(((self.neon[15] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v15h2 => ILVal::Short(((self.neon[15] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v15h3 => ILVal::Short(((self.neon[15] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v15h4 => ILVal::Short(((self.neon[15] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v15h5 => ILVal::Short(((self.neon[15] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v15h6 => ILVal::Short(((self.neon[15] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v15h7 => ILVal::Short(((self.neon[15] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v16h0 => ILVal::Short(((self.neon[16] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v16h1 => ILVal::Short(((self.neon[16] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v16h2 => ILVal::Short(((self.neon[16] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v16h3 => ILVal::Short(((self.neon[16] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v16h4 => ILVal::Short(((self.neon[16] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v16h5 => ILVal::Short(((self.neon[16] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v16h6 => ILVal::Short(((self.neon[16] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v16h7 => ILVal::Short(((self.neon[16] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v17h0 => ILVal::Short(((self.neon[17] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v17h1 => ILVal::Short(((self.neon[17] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v17h2 => ILVal::Short(((self.neon[17] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v17h3 => ILVal::Short(((self.neon[17] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v17h4 => ILVal::Short(((self.neon[17] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v17h5 => ILVal::Short(((self.neon[17] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v17h6 => ILVal::Short(((self.neon[17] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v17h7 => ILVal::Short(((self.neon[17] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v18h0 => ILVal::Short(((self.neon[18] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v18h1 => ILVal::Short(((self.neon[18] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v18h2 => ILVal::Short(((self.neon[18] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v18h3 => ILVal::Short(((self.neon[18] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v18h4 => ILVal::Short(((self.neon[18] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v18h5 => ILVal::Short(((self.neon[18] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v18h6 => ILVal::Short(((self.neon[18] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v18h7 => ILVal::Short(((self.neon[18] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v19h0 => ILVal::Short(((self.neon[19] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v19h1 => ILVal::Short(((self.neon[19] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v19h2 => ILVal::Short(((self.neon[19] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v19h3 => ILVal::Short(((self.neon[19] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v19h4 => ILVal::Short(((self.neon[19] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v19h5 => ILVal::Short(((self.neon[19] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v19h6 => ILVal::Short(((self.neon[19] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v19h7 => ILVal::Short(((self.neon[19] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v20h0 => ILVal::Short(((self.neon[20] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v20h1 => ILVal::Short(((self.neon[20] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v20h2 => ILVal::Short(((self.neon[20] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v20h3 => ILVal::Short(((self.neon[20] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v20h4 => ILVal::Short(((self.neon[20] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v20h5 => ILVal::Short(((self.neon[20] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v20h6 => ILVal::Short(((self.neon[20] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v20h7 => ILVal::Short(((self.neon[20] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v21h0 => ILVal::Short(((self.neon[21] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v21h1 => ILVal::Short(((self.neon[21] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v21h2 => ILVal::Short(((self.neon[21] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v21h3 => ILVal::Short(((self.neon[21] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v21h4 => ILVal::Short(((self.neon[21] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v21h5 => ILVal::Short(((self.neon[21] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v21h6 => ILVal::Short(((self.neon[21] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v21h7 => ILVal::Short(((self.neon[21] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v22h0 => ILVal::Short(((self.neon[22] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v22h1 => ILVal::Short(((self.neon[22] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v22h2 => ILVal::Short(((self.neon[22] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v22h3 => ILVal::Short(((self.neon[22] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v22h4 => ILVal::Short(((self.neon[22] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v22h5 => ILVal::Short(((self.neon[22] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v22h6 => ILVal::Short(((self.neon[22] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v22h7 => ILVal::Short(((self.neon[22] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v23h0 => ILVal::Short(((self.neon[23] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v23h1 => ILVal::Short(((self.neon[23] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v23h2 => ILVal::Short(((self.neon[23] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v23h3 => ILVal::Short(((self.neon[23] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v23h4 => ILVal::Short(((self.neon[23] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v23h5 => ILVal::Short(((self.neon[23] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v23h6 => ILVal::Short(((self.neon[23] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v23h7 => ILVal::Short(((self.neon[23] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v24h0 => ILVal::Short(((self.neon[24] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v24h1 => ILVal::Short(((self.neon[24] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v24h2 => ILVal::Short(((self.neon[24] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v24h3 => ILVal::Short(((self.neon[24] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v24h4 => ILVal::Short(((self.neon[24] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v24h5 => ILVal::Short(((self.neon[24] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v24h6 => ILVal::Short(((self.neon[24] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v24h7 => ILVal::Short(((self.neon[24] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v25h0 => ILVal::Short(((self.neon[25] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v25h1 => ILVal::Short(((self.neon[25] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v25h2 => ILVal::Short(((self.neon[25] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v25h3 => ILVal::Short(((self.neon[25] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v25h4 => ILVal::Short(((self.neon[25] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v25h5 => ILVal::Short(((self.neon[25] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v25h6 => ILVal::Short(((self.neon[25] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v25h7 => ILVal::Short(((self.neon[25] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v26h0 => ILVal::Short(((self.neon[26] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v26h1 => ILVal::Short(((self.neon[26] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v26h2 => ILVal::Short(((self.neon[26] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v26h3 => ILVal::Short(((self.neon[26] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v26h4 => ILVal::Short(((self.neon[26] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v26h5 => ILVal::Short(((self.neon[26] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v26h6 => ILVal::Short(((self.neon[26] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v26h7 => ILVal::Short(((self.neon[26] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v27h0 => ILVal::Short(((self.neon[27] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v27h1 => ILVal::Short(((self.neon[27] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v27h2 => ILVal::Short(((self.neon[27] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v27h3 => ILVal::Short(((self.neon[27] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v27h4 => ILVal::Short(((self.neon[27] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v27h5 => ILVal::Short(((self.neon[27] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v27h6 => ILVal::Short(((self.neon[27] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v27h7 => ILVal::Short(((self.neon[27] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v28h0 => ILVal::Short(((self.neon[28] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v28h1 => ILVal::Short(((self.neon[28] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v28h2 => ILVal::Short(((self.neon[28] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v28h3 => ILVal::Short(((self.neon[28] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v28h4 => ILVal::Short(((self.neon[28] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v28h5 => ILVal::Short(((self.neon[28] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v28h6 => ILVal::Short(((self.neon[28] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v28h7 => ILVal::Short(((self.neon[28] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v29h0 => ILVal::Short(((self.neon[29] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v29h1 => ILVal::Short(((self.neon[29] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v29h2 => ILVal::Short(((self.neon[29] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v29h3 => ILVal::Short(((self.neon[29] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v29h4 => ILVal::Short(((self.neon[29] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v29h5 => ILVal::Short(((self.neon[29] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v29h6 => ILVal::Short(((self.neon[29] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v29h7 => ILVal::Short(((self.neon[29] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v30h0 => ILVal::Short(((self.neon[30] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v30h1 => ILVal::Short(((self.neon[30] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v30h2 => ILVal::Short(((self.neon[30] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v30h3 => ILVal::Short(((self.neon[30] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v30h4 => ILVal::Short(((self.neon[30] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v30h5 => ILVal::Short(((self.neon[30] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v30h6 => ILVal::Short(((self.neon[30] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v30h7 => ILVal::Short(((self.neon[30] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v31h0 => ILVal::Short(((self.neon[31] >> (0 * 16)) & 0xffff) as u16),
            Arm64Reg::v31h1 => ILVal::Short(((self.neon[31] >> (1 * 16)) & 0xffff) as u16),
            Arm64Reg::v31h2 => ILVal::Short(((self.neon[31] >> (2 * 16)) & 0xffff) as u16),
            Arm64Reg::v31h3 => ILVal::Short(((self.neon[31] >> (3 * 16)) & 0xffff) as u16),
            Arm64Reg::v31h4 => ILVal::Short(((self.neon[31] >> (4 * 16)) & 0xffff) as u16),
            Arm64Reg::v31h5 => ILVal::Short(((self.neon[31] >> (5 * 16)) & 0xffff) as u16),
            Arm64Reg::v31h6 => ILVal::Short(((self.neon[31] >> (6 * 16)) & 0xffff) as u16),
            Arm64Reg::v31h7 => ILVal::Short(((self.neon[31] >> (7 * 16)) & 0xffff) as u16),
            Arm64Reg::v0s0 => ILVal::Word(((self.neon[0] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v0s1 => ILVal::Word(((self.neon[0] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v0s2 => ILVal::Word(((self.neon[0] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v0s3 => ILVal::Word(((self.neon[0] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v1s0 => ILVal::Word(((self.neon[1] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v1s1 => ILVal::Word(((self.neon[1] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v1s2 => ILVal::Word(((self.neon[1] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v1s3 => ILVal::Word(((self.neon[1] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v2s0 => ILVal::Word(((self.neon[2] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v2s1 => ILVal::Word(((self.neon[2] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v2s2 => ILVal::Word(((self.neon[2] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v2s3 => ILVal::Word(((self.neon[2] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v3s0 => ILVal::Word(((self.neon[3] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v3s1 => ILVal::Word(((self.neon[3] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v3s2 => ILVal::Word(((self.neon[3] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v3s3 => ILVal::Word(((self.neon[3] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v4s0 => ILVal::Word(((self.neon[4] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v4s1 => ILVal::Word(((self.neon[4] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v4s2 => ILVal::Word(((self.neon[4] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v4s3 => ILVal::Word(((self.neon[4] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v5s0 => ILVal::Word(((self.neon[5] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v5s1 => ILVal::Word(((self.neon[5] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v5s2 => ILVal::Word(((self.neon[5] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v5s3 => ILVal::Word(((self.neon[5] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v6s0 => ILVal::Word(((self.neon[6] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v6s1 => ILVal::Word(((self.neon[6] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v6s2 => ILVal::Word(((self.neon[6] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v6s3 => ILVal::Word(((self.neon[6] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v7s0 => ILVal::Word(((self.neon[7] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v7s1 => ILVal::Word(((self.neon[7] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v7s2 => ILVal::Word(((self.neon[7] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v7s3 => ILVal::Word(((self.neon[7] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v8s0 => ILVal::Word(((self.neon[8] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v8s1 => ILVal::Word(((self.neon[8] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v8s2 => ILVal::Word(((self.neon[8] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v8s3 => ILVal::Word(((self.neon[8] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v9s0 => ILVal::Word(((self.neon[9] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v9s1 => ILVal::Word(((self.neon[9] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v9s2 => ILVal::Word(((self.neon[9] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v9s3 => ILVal::Word(((self.neon[9] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v10s0 => ILVal::Word(((self.neon[10] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v10s1 => ILVal::Word(((self.neon[10] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v10s2 => ILVal::Word(((self.neon[10] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v10s3 => ILVal::Word(((self.neon[10] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v11s0 => ILVal::Word(((self.neon[11] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v11s1 => ILVal::Word(((self.neon[11] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v11s2 => ILVal::Word(((self.neon[11] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v11s3 => ILVal::Word(((self.neon[11] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v12s0 => ILVal::Word(((self.neon[12] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v12s1 => ILVal::Word(((self.neon[12] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v12s2 => ILVal::Word(((self.neon[12] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v12s3 => ILVal::Word(((self.neon[12] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v13s0 => ILVal::Word(((self.neon[13] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v13s1 => ILVal::Word(((self.neon[13] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v13s2 => ILVal::Word(((self.neon[13] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v13s3 => ILVal::Word(((self.neon[13] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v14s0 => ILVal::Word(((self.neon[14] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v14s1 => ILVal::Word(((self.neon[14] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v14s2 => ILVal::Word(((self.neon[14] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v14s3 => ILVal::Word(((self.neon[14] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v15s0 => ILVal::Word(((self.neon[15] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v15s1 => ILVal::Word(((self.neon[15] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v15s2 => ILVal::Word(((self.neon[15] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v15s3 => ILVal::Word(((self.neon[15] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v16s0 => ILVal::Word(((self.neon[16] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v16s1 => ILVal::Word(((self.neon[16] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v16s2 => ILVal::Word(((self.neon[16] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v16s3 => ILVal::Word(((self.neon[16] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v17s0 => ILVal::Word(((self.neon[17] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v17s1 => ILVal::Word(((self.neon[17] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v17s2 => ILVal::Word(((self.neon[17] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v17s3 => ILVal::Word(((self.neon[17] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v18s0 => ILVal::Word(((self.neon[18] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v18s1 => ILVal::Word(((self.neon[18] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v18s2 => ILVal::Word(((self.neon[18] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v18s3 => ILVal::Word(((self.neon[18] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v19s0 => ILVal::Word(((self.neon[19] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v19s1 => ILVal::Word(((self.neon[19] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v19s2 => ILVal::Word(((self.neon[19] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v19s3 => ILVal::Word(((self.neon[19] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v20s0 => ILVal::Word(((self.neon[20] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v20s1 => ILVal::Word(((self.neon[20] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v20s2 => ILVal::Word(((self.neon[20] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v20s3 => ILVal::Word(((self.neon[20] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v21s0 => ILVal::Word(((self.neon[21] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v21s1 => ILVal::Word(((self.neon[21] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v21s2 => ILVal::Word(((self.neon[21] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v21s3 => ILVal::Word(((self.neon[21] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v22s0 => ILVal::Word(((self.neon[22] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v22s1 => ILVal::Word(((self.neon[22] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v22s2 => ILVal::Word(((self.neon[22] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v22s3 => ILVal::Word(((self.neon[22] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v23s0 => ILVal::Word(((self.neon[23] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v23s1 => ILVal::Word(((self.neon[23] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v23s2 => ILVal::Word(((self.neon[23] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v23s3 => ILVal::Word(((self.neon[23] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v24s0 => ILVal::Word(((self.neon[24] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v24s1 => ILVal::Word(((self.neon[24] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v24s2 => ILVal::Word(((self.neon[24] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v24s3 => ILVal::Word(((self.neon[24] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v25s0 => ILVal::Word(((self.neon[25] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v25s1 => ILVal::Word(((self.neon[25] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v25s2 => ILVal::Word(((self.neon[25] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v25s3 => ILVal::Word(((self.neon[25] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v26s0 => ILVal::Word(((self.neon[26] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v26s1 => ILVal::Word(((self.neon[26] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v26s2 => ILVal::Word(((self.neon[26] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v26s3 => ILVal::Word(((self.neon[26] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v27s0 => ILVal::Word(((self.neon[27] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v27s1 => ILVal::Word(((self.neon[27] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v27s2 => ILVal::Word(((self.neon[27] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v27s3 => ILVal::Word(((self.neon[27] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v28s0 => ILVal::Word(((self.neon[28] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v28s1 => ILVal::Word(((self.neon[28] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v28s2 => ILVal::Word(((self.neon[28] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v28s3 => ILVal::Word(((self.neon[28] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v29s0 => ILVal::Word(((self.neon[29] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v29s1 => ILVal::Word(((self.neon[29] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v29s2 => ILVal::Word(((self.neon[29] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v29s3 => ILVal::Word(((self.neon[29] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v30s0 => ILVal::Word(((self.neon[30] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v30s1 => ILVal::Word(((self.neon[30] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v30s2 => ILVal::Word(((self.neon[30] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v30s3 => ILVal::Word(((self.neon[30] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v31s0 => ILVal::Word(((self.neon[31] >> (0 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v31s1 => ILVal::Word(((self.neon[31] >> (1 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v31s2 => ILVal::Word(((self.neon[31] >> (2 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v31s3 => ILVal::Word(((self.neon[31] >> (3 * 32)) & 0xffffffff) as u32),
            Arm64Reg::v0d0 => ILVal::Quad(((self.neon[0] >> (0 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v0d1 => ILVal::Quad(((self.neon[0] >> (1 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v1d0 => ILVal::Quad(((self.neon[1] >> (0 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v1d1 => ILVal::Quad(((self.neon[1] >> (1 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v2d0 => ILVal::Quad(((self.neon[2] >> (0 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v2d1 => ILVal::Quad(((self.neon[2] >> (1 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v3d0 => ILVal::Quad(((self.neon[3] >> (0 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v3d1 => ILVal::Quad(((self.neon[3] >> (1 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v4d0 => ILVal::Quad(((self.neon[4] >> (0 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v4d1 => ILVal::Quad(((self.neon[4] >> (1 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v5d0 => ILVal::Quad(((self.neon[5] >> (0 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v5d1 => ILVal::Quad(((self.neon[5] >> (1 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v6d0 => ILVal::Quad(((self.neon[6] >> (0 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v6d1 => ILVal::Quad(((self.neon[6] >> (1 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v7d0 => ILVal::Quad(((self.neon[7] >> (0 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v7d1 => ILVal::Quad(((self.neon[7] >> (1 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v8d0 => ILVal::Quad(((self.neon[8] >> (0 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v8d1 => ILVal::Quad(((self.neon[8] >> (1 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v9d0 => ILVal::Quad(((self.neon[9] >> (0 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v9d1 => ILVal::Quad(((self.neon[9] >> (1 * 64)) & 0xffffffffffffffff) as u64),
            Arm64Reg::v10d0 => {
                ILVal::Quad(((self.neon[10] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v10d1 => {
                ILVal::Quad(((self.neon[10] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v11d0 => {
                ILVal::Quad(((self.neon[11] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v11d1 => {
                ILVal::Quad(((self.neon[11] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v12d0 => {
                ILVal::Quad(((self.neon[12] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v12d1 => {
                ILVal::Quad(((self.neon[12] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v13d0 => {
                ILVal::Quad(((self.neon[13] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v13d1 => {
                ILVal::Quad(((self.neon[13] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v14d0 => {
                ILVal::Quad(((self.neon[14] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v14d1 => {
                ILVal::Quad(((self.neon[14] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v15d0 => {
                ILVal::Quad(((self.neon[15] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v15d1 => {
                ILVal::Quad(((self.neon[15] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v16d0 => {
                ILVal::Quad(((self.neon[16] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v16d1 => {
                ILVal::Quad(((self.neon[16] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v17d0 => {
                ILVal::Quad(((self.neon[17] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v17d1 => {
                ILVal::Quad(((self.neon[17] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v18d0 => {
                ILVal::Quad(((self.neon[18] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v18d1 => {
                ILVal::Quad(((self.neon[18] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v19d0 => {
                ILVal::Quad(((self.neon[19] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v19d1 => {
                ILVal::Quad(((self.neon[19] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v20d0 => {
                ILVal::Quad(((self.neon[20] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v20d1 => {
                ILVal::Quad(((self.neon[20] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v21d0 => {
                ILVal::Quad(((self.neon[21] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v21d1 => {
                ILVal::Quad(((self.neon[21] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v22d0 => {
                ILVal::Quad(((self.neon[22] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v22d1 => {
                ILVal::Quad(((self.neon[22] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v23d0 => {
                ILVal::Quad(((self.neon[23] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v23d1 => {
                ILVal::Quad(((self.neon[23] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v24d0 => {
                ILVal::Quad(((self.neon[24] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v24d1 => {
                ILVal::Quad(((self.neon[24] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v25d0 => {
                ILVal::Quad(((self.neon[25] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v25d1 => {
                ILVal::Quad(((self.neon[25] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v26d0 => {
                ILVal::Quad(((self.neon[26] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v26d1 => {
                ILVal::Quad(((self.neon[26] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v27d0 => {
                ILVal::Quad(((self.neon[27] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v27d1 => {
                ILVal::Quad(((self.neon[27] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v28d0 => {
                ILVal::Quad(((self.neon[28] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v28d1 => {
                ILVal::Quad(((self.neon[28] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v29d0 => {
                ILVal::Quad(((self.neon[29] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v29d1 => {
                ILVal::Quad(((self.neon[29] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v30d0 => {
                ILVal::Quad(((self.neon[30] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v30d1 => {
                ILVal::Quad(((self.neon[30] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v31d0 => {
                ILVal::Quad(((self.neon[31] >> (0 * 64)) & 0xffffffffffffffff) as u64)
            }
            Arm64Reg::v31d1 => {
                ILVal::Quad(((self.neon[31] >> (1 * 64)) & 0xffffffffffffffff) as u64)
            }
        }
    }
}

impl Index<Arm64Reg> for Arm64State {
    type Output = u64;

    fn index(&self, index: Arm64Reg) -> &Self::Output {
        match index {
            Arm64Reg::x0 => &self.gregs[0],
            Arm64Reg::x1 => &self.gregs[1],
            Arm64Reg::x2 => &self.gregs[2],
            Arm64Reg::x3 => &self.gregs[3],
            Arm64Reg::x4 => &self.gregs[4],
            Arm64Reg::x5 => &self.gregs[5],
            Arm64Reg::x6 => &self.gregs[6],
            Arm64Reg::x7 => &self.gregs[7],
            Arm64Reg::x8 => &self.gregs[8],
            Arm64Reg::x9 => &self.gregs[9],
            Arm64Reg::x10 => &self.gregs[10],
            Arm64Reg::x11 => &self.gregs[11],
            Arm64Reg::x12 => &self.gregs[12],
            Arm64Reg::x13 => &self.gregs[13],
            Arm64Reg::x14 => &self.gregs[14],
            Arm64Reg::x15 => &self.gregs[15],
            Arm64Reg::x16 => &self.gregs[16],
            Arm64Reg::x17 => &self.gregs[17],
            Arm64Reg::x18 => &self.gregs[18],
            Arm64Reg::x19 => &self.gregs[19],
            Arm64Reg::x20 => &self.gregs[20],
            Arm64Reg::x21 => &self.gregs[21],
            Arm64Reg::x22 => &self.gregs[22],
            Arm64Reg::x23 => &self.gregs[23],
            Arm64Reg::x24 => &self.gregs[24],
            Arm64Reg::x25 => &self.gregs[25],
            Arm64Reg::x26 => &self.gregs[26],
            Arm64Reg::x27 => &self.gregs[27],
            Arm64Reg::x28 => &self.gregs[28],
            Arm64Reg::fp => &self.gregs[29],
            Arm64Reg::lr => &self.gregs[30],
            Arm64Reg::sp => &self.gregs[31],
            Arm64Reg::syscall_info => &self.syscall_info,
            _ => panic!("Can only index full sized registers"),
        }
    }
}

impl IndexMut<Arm64Reg> for Arm64State {
    fn index_mut(&mut self, index: Arm64Reg) -> &mut Self::Output {
        match index {
            Arm64Reg::x0 => &mut self.gregs[0],
            Arm64Reg::x1 => &mut self.gregs[1],
            Arm64Reg::x2 => &mut self.gregs[2],
            Arm64Reg::x3 => &mut self.gregs[3],
            Arm64Reg::x4 => &mut self.gregs[4],
            Arm64Reg::x5 => &mut self.gregs[5],
            Arm64Reg::x6 => &mut self.gregs[6],
            Arm64Reg::x7 => &mut self.gregs[7],
            Arm64Reg::x8 => &mut self.gregs[8],
            Arm64Reg::x9 => &mut self.gregs[9],
            Arm64Reg::x10 => &mut self.gregs[10],
            Arm64Reg::x11 => &mut self.gregs[11],
            Arm64Reg::x12 => &mut self.gregs[12],
            Arm64Reg::x13 => &mut self.gregs[13],
            Arm64Reg::x14 => &mut self.gregs[14],
            Arm64Reg::x15 => &mut self.gregs[15],
            Arm64Reg::x16 => &mut self.gregs[16],
            Arm64Reg::x17 => &mut self.gregs[17],
            Arm64Reg::x18 => &mut self.gregs[18],
            Arm64Reg::x19 => &mut self.gregs[19],
            Arm64Reg::x20 => &mut self.gregs[20],
            Arm64Reg::x21 => &mut self.gregs[21],
            Arm64Reg::x22 => &mut self.gregs[22],
            Arm64Reg::x23 => &mut self.gregs[23],
            Arm64Reg::x24 => &mut self.gregs[24],
            Arm64Reg::x25 => &mut self.gregs[25],
            Arm64Reg::x26 => &mut self.gregs[26],
            Arm64Reg::x27 => &mut self.gregs[27],
            Arm64Reg::x28 => &mut self.gregs[28],
            Arm64Reg::fp => &mut self.gregs[29],
            Arm64Reg::lr => &mut self.gregs[30],
            Arm64Reg::sp => &mut self.gregs[31],
            Arm64Reg::syscall_info => &mut self.syscall_info,
            _ => panic!("Can only index full sized registers"),
        }
    }
}

#[allow(non_camel_case_types)]
#[repr(u32)]
#[derive(FromId, Debug, Clone, Copy, PartialEq, Eq)]
pub enum Arm64Reg {
    // General purpose registers for the integer instruction set.
    w0 = 1,
    w1 = 2,
    w2 = 3,
    w3 = 4,
    w4 = 5,
    w5 = 6,
    w6 = 7,
    w7 = 8,
    w8 = 9,
    w9 = 10,
    w10 = 11,
    w11 = 12,
    w12 = 13,
    w13 = 14,
    w14 = 15,
    w15 = 16,
    w16 = 17,
    w17 = 18,
    w18 = 19,
    w19 = 20,
    w20 = 21,
    w21 = 22,
    w22 = 23,
    w23 = 24,
    w24 = 25,
    w25 = 26,
    w26 = 27,
    w27 = 28,
    w28 = 29,
    w29 = 30,
    w30 = 31,
    wsp = 33,
    x0 = 34,
    x1 = 35,
    x2 = 36,
    x3 = 37,
    x4 = 38,
    x5 = 39,
    x6 = 40,
    x7 = 41,
    x8 = 42,
    x9 = 43,
    x10 = 44,
    x11 = 45,
    x12 = 46,
    x13 = 47,
    x14 = 48,
    x15 = 49,
    x16 = 50,
    x17 = 51,
    x18 = 52,
    x19 = 53,
    x20 = 54,
    x21 = 55,
    x22 = 56,
    x23 = 57,
    x24 = 58,
    x25 = 59,
    x26 = 60,
    x27 = 61,
    x28 = 62,
    fp = 63,
    lr = 64,
    sp = 66,
    // Arm NEON registers.
    s0 = 163,
    s1 = 164,
    s2 = 165,
    s3 = 166,
    s4 = 167,
    s5 = 168,
    s6 = 169,
    s7 = 170,
    s8 = 171,
    s9 = 172,
    s10 = 173,
    s11 = 174,
    s12 = 175,
    s13 = 176,
    s14 = 177,
    s15 = 178,
    s16 = 179,
    s17 = 180,
    s18 = 181,
    s19 = 182,
    s20 = 183,
    s21 = 184,
    s22 = 185,
    s23 = 186,
    s24 = 187,
    s25 = 188,
    s26 = 189,
    s27 = 190,
    s28 = 191,
    s29 = 192,
    s30 = 193,
    s31 = 194,
    d0 = 195,
    d1 = 196,
    d2 = 197,
    d3 = 198,
    d4 = 199,
    d5 = 200,
    d6 = 201,
    d7 = 202,
    d8 = 203,
    d9 = 204,
    d10 = 205,
    d11 = 206,
    d12 = 207,
    d13 = 208,
    d14 = 209,
    d15 = 210,
    d16 = 211,
    d17 = 212,
    d18 = 213,
    d19 = 214,
    d20 = 215,
    d21 = 216,
    d22 = 217,
    d23 = 218,
    d24 = 219,
    d25 = 220,
    d26 = 221,
    d27 = 222,
    d28 = 223,
    d29 = 224,
    d30 = 225,
    d31 = 226,
    q0 = 227,
    q1 = 228,
    q2 = 229,
    q3 = 230,
    q4 = 231,
    q5 = 232,
    q6 = 233,
    q7 = 234,
    q8 = 235,
    q9 = 236,
    q10 = 237,
    q11 = 238,
    q12 = 239,
    q13 = 240,
    q14 = 241,
    q15 = 242,
    q16 = 243,
    q17 = 244,
    q18 = 245,
    q19 = 246,
    q20 = 247,
    q21 = 248,
    q22 = 249,
    q23 = 250,
    q24 = 251,
    q25 = 252,
    q26 = 253,
    q27 = 254,
    q28 = 255,
    q29 = 256,
    q30 = 257,
    q31 = 258,
    v0b0 = 259,
    v0b1 = 260,
    v0b2 = 261,
    v0b3 = 262,
    v0b4 = 263,
    v0b5 = 264,
    v0b6 = 265,
    v0b7 = 266,
    v0b8 = 267,
    v0b9 = 268,
    v0b10 = 269,
    v0b11 = 270,
    v0b12 = 271,
    v0b13 = 272,
    v0b14 = 273,
    v0b15 = 274,
    v1b0 = 275,
    v1b1 = 276,
    v1b2 = 277,
    v1b3 = 278,
    v1b4 = 279,
    v1b5 = 280,
    v1b6 = 281,
    v1b7 = 282,
    v1b8 = 283,
    v1b9 = 284,
    v1b10 = 285,
    v1b11 = 286,
    v1b12 = 287,
    v1b13 = 288,
    v1b14 = 289,
    v1b15 = 290,
    v2b0 = 291,
    v2b1 = 292,
    v2b2 = 293,
    v2b3 = 294,
    v2b4 = 295,
    v2b5 = 296,
    v2b6 = 297,
    v2b7 = 298,
    v2b8 = 299,
    v2b9 = 300,
    v2b10 = 301,
    v2b11 = 302,
    v2b12 = 303,
    v2b13 = 304,
    v2b14 = 305,
    v2b15 = 306,
    v3b0 = 307,
    v3b1 = 308,
    v3b2 = 309,
    v3b3 = 310,
    v3b4 = 311,
    v3b5 = 312,
    v3b6 = 313,
    v3b7 = 314,
    v3b8 = 315,
    v3b9 = 316,
    v3b10 = 317,
    v3b11 = 318,
    v3b12 = 319,
    v3b13 = 320,
    v3b14 = 321,
    v3b15 = 322,
    v4b0 = 323,
    v4b1 = 324,
    v4b2 = 325,
    v4b3 = 326,
    v4b4 = 327,
    v4b5 = 328,
    v4b6 = 329,
    v4b7 = 330,
    v4b8 = 331,
    v4b9 = 332,
    v4b10 = 333,
    v4b11 = 334,
    v4b12 = 335,
    v4b13 = 336,
    v4b14 = 337,
    v4b15 = 338,
    v5b0 = 339,
    v5b1 = 340,
    v5b2 = 341,
    v5b3 = 342,
    v5b4 = 343,
    v5b5 = 344,
    v5b6 = 345,
    v5b7 = 346,
    v5b8 = 347,
    v5b9 = 348,
    v5b10 = 349,
    v5b11 = 350,
    v5b12 = 351,
    v5b13 = 352,
    v5b14 = 353,
    v5b15 = 354,
    v6b0 = 355,
    v6b1 = 356,
    v6b2 = 357,
    v6b3 = 358,
    v6b4 = 359,
    v6b5 = 360,
    v6b6 = 361,
    v6b7 = 362,
    v6b8 = 363,
    v6b9 = 364,
    v6b10 = 365,
    v6b11 = 366,
    v6b12 = 367,
    v6b13 = 368,
    v6b14 = 369,
    v6b15 = 370,
    v7b0 = 371,
    v7b1 = 372,
    v7b2 = 373,
    v7b3 = 374,
    v7b4 = 375,
    v7b5 = 376,
    v7b6 = 377,
    v7b7 = 378,
    v7b8 = 379,
    v7b9 = 380,
    v7b10 = 381,
    v7b11 = 382,
    v7b12 = 383,
    v7b13 = 384,
    v7b14 = 385,
    v7b15 = 386,
    v8b0 = 387,
    v8b1 = 388,
    v8b2 = 389,
    v8b3 = 390,
    v8b4 = 391,
    v8b5 = 392,
    v8b6 = 393,
    v8b7 = 394,
    v8b8 = 395,
    v8b9 = 396,
    v8b10 = 397,
    v8b11 = 398,
    v8b12 = 399,
    v8b13 = 400,
    v8b14 = 401,
    v8b15 = 402,
    v9b0 = 403,
    v9b1 = 404,
    v9b2 = 405,
    v9b3 = 406,
    v9b4 = 407,
    v9b5 = 408,
    v9b6 = 409,
    v9b7 = 410,
    v9b8 = 411,
    v9b9 = 412,
    v9b10 = 413,
    v9b11 = 414,
    v9b12 = 415,
    v9b13 = 416,
    v9b14 = 417,
    v9b15 = 418,
    v10b0 = 419,
    v10b1 = 420,
    v10b2 = 421,
    v10b3 = 422,
    v10b4 = 423,
    v10b5 = 424,
    v10b6 = 425,
    v10b7 = 426,
    v10b8 = 427,
    v10b9 = 428,
    v10b10 = 429,
    v10b11 = 430,
    v10b12 = 431,
    v10b13 = 432,
    v10b14 = 433,
    v10b15 = 434,
    v11b0 = 435,
    v11b1 = 436,
    v11b2 = 437,
    v11b3 = 438,
    v11b4 = 439,
    v11b5 = 440,
    v11b6 = 441,
    v11b7 = 442,
    v11b8 = 443,
    v11b9 = 444,
    v11b10 = 445,
    v11b11 = 446,
    v11b12 = 447,
    v11b13 = 448,
    v11b14 = 449,
    v11b15 = 450,
    v12b0 = 451,
    v12b1 = 452,
    v12b2 = 453,
    v12b3 = 454,
    v12b4 = 455,
    v12b5 = 456,
    v12b6 = 457,
    v12b7 = 458,
    v12b8 = 459,
    v12b9 = 460,
    v12b10 = 461,
    v12b11 = 462,
    v12b12 = 463,
    v12b13 = 464,
    v12b14 = 465,
    v12b15 = 466,
    v13b0 = 467,
    v13b1 = 468,
    v13b2 = 469,
    v13b3 = 470,
    v13b4 = 471,
    v13b5 = 472,
    v13b6 = 473,
    v13b7 = 474,
    v13b8 = 475,
    v13b9 = 476,
    v13b10 = 477,
    v13b11 = 478,
    v13b12 = 479,
    v13b13 = 480,
    v13b14 = 481,
    v13b15 = 482,
    v14b0 = 483,
    v14b1 = 484,
    v14b2 = 485,
    v14b3 = 486,
    v14b4 = 487,
    v14b5 = 488,
    v14b6 = 489,
    v14b7 = 490,
    v14b8 = 491,
    v14b9 = 492,
    v14b10 = 493,
    v14b11 = 494,
    v14b12 = 495,
    v14b13 = 496,
    v14b14 = 497,
    v14b15 = 498,
    v15b0 = 499,
    v15b1 = 500,
    v15b2 = 501,
    v15b3 = 502,
    v15b4 = 503,
    v15b5 = 504,
    v15b6 = 505,
    v15b7 = 506,
    v15b8 = 507,
    v15b9 = 508,
    v15b10 = 509,
    v15b11 = 510,
    v15b12 = 511,
    v15b13 = 512,
    v15b14 = 513,
    v15b15 = 514,
    v16b0 = 515,
    v16b1 = 516,
    v16b2 = 517,
    v16b3 = 518,
    v16b4 = 519,
    v16b5 = 520,
    v16b6 = 521,
    v16b7 = 522,
    v16b8 = 523,
    v16b9 = 524,
    v16b10 = 525,
    v16b11 = 526,
    v16b12 = 527,
    v16b13 = 528,
    v16b14 = 529,
    v16b15 = 530,
    v17b0 = 531,
    v17b1 = 532,
    v17b2 = 533,
    v17b3 = 534,
    v17b4 = 535,
    v17b5 = 536,
    v17b6 = 537,
    v17b7 = 538,
    v17b8 = 539,
    v17b9 = 540,
    v17b10 = 541,
    v17b11 = 542,
    v17b12 = 543,
    v17b13 = 544,
    v17b14 = 545,
    v17b15 = 546,
    v18b0 = 547,
    v18b1 = 548,
    v18b2 = 549,
    v18b3 = 550,
    v18b4 = 551,
    v18b5 = 552,
    v18b6 = 553,
    v18b7 = 554,
    v18b8 = 555,
    v18b9 = 556,
    v18b10 = 557,
    v18b11 = 558,
    v18b12 = 559,
    v18b13 = 560,
    v18b14 = 561,
    v18b15 = 562,
    v19b0 = 563,
    v19b1 = 564,
    v19b2 = 565,
    v19b3 = 566,
    v19b4 = 567,
    v19b5 = 568,
    v19b6 = 569,
    v19b7 = 570,
    v19b8 = 571,
    v19b9 = 572,
    v19b10 = 573,
    v19b11 = 574,
    v19b12 = 575,
    v19b13 = 576,
    v19b14 = 577,
    v19b15 = 578,
    v20b0 = 579,
    v20b1 = 580,
    v20b2 = 581,
    v20b3 = 582,
    v20b4 = 583,
    v20b5 = 584,
    v20b6 = 585,
    v20b7 = 586,
    v20b8 = 587,
    v20b9 = 588,
    v20b10 = 589,
    v20b11 = 590,
    v20b12 = 591,
    v20b13 = 592,
    v20b14 = 593,
    v20b15 = 594,
    v21b0 = 595,
    v21b1 = 596,
    v21b2 = 597,
    v21b3 = 598,
    v21b4 = 599,
    v21b5 = 600,
    v21b6 = 601,
    v21b7 = 602,
    v21b8 = 603,
    v21b9 = 604,
    v21b10 = 605,
    v21b11 = 606,
    v21b12 = 607,
    v21b13 = 608,
    v21b14 = 609,
    v21b15 = 610,
    v22b0 = 611,
    v22b1 = 612,
    v22b2 = 613,
    v22b3 = 614,
    v22b4 = 615,
    v22b5 = 616,
    v22b6 = 617,
    v22b7 = 618,
    v22b8 = 619,
    v22b9 = 620,
    v22b10 = 621,
    v22b11 = 622,
    v22b12 = 623,
    v22b13 = 624,
    v22b14 = 625,
    v22b15 = 626,
    v23b0 = 627,
    v23b1 = 628,
    v23b2 = 629,
    v23b3 = 630,
    v23b4 = 631,
    v23b5 = 632,
    v23b6 = 633,
    v23b7 = 634,
    v23b8 = 635,
    v23b9 = 636,
    v23b10 = 637,
    v23b11 = 638,
    v23b12 = 639,
    v23b13 = 640,
    v23b14 = 641,
    v23b15 = 642,
    v24b0 = 643,
    v24b1 = 644,
    v24b2 = 645,
    v24b3 = 646,
    v24b4 = 647,
    v24b5 = 648,
    v24b6 = 649,
    v24b7 = 650,
    v24b8 = 651,
    v24b9 = 652,
    v24b10 = 653,
    v24b11 = 654,
    v24b12 = 655,
    v24b13 = 656,
    v24b14 = 657,
    v24b15 = 658,
    v25b0 = 659,
    v25b1 = 660,
    v25b2 = 661,
    v25b3 = 662,
    v25b4 = 663,
    v25b5 = 664,
    v25b6 = 665,
    v25b7 = 666,
    v25b8 = 667,
    v25b9 = 668,
    v25b10 = 669,
    v25b11 = 670,
    v25b12 = 671,
    v25b13 = 672,
    v25b14 = 673,
    v25b15 = 674,
    v26b0 = 675,
    v26b1 = 676,
    v26b2 = 677,
    v26b3 = 678,
    v26b4 = 679,
    v26b5 = 680,
    v26b6 = 681,
    v26b7 = 682,
    v26b8 = 683,
    v26b9 = 684,
    v26b10 = 685,
    v26b11 = 686,
    v26b12 = 687,
    v26b13 = 688,
    v26b14 = 689,
    v26b15 = 690,
    v27b0 = 691,
    v27b1 = 692,
    v27b2 = 693,
    v27b3 = 694,
    v27b4 = 695,
    v27b5 = 696,
    v27b6 = 697,
    v27b7 = 698,
    v27b8 = 699,
    v27b9 = 700,
    v27b10 = 701,
    v27b11 = 702,
    v27b12 = 703,
    v27b13 = 704,
    v27b14 = 705,
    v27b15 = 706,
    v28b0 = 707,
    v28b1 = 708,
    v28b2 = 709,
    v28b3 = 710,
    v28b4 = 711,
    v28b5 = 712,
    v28b6 = 713,
    v28b7 = 714,
    v28b8 = 715,
    v28b9 = 716,
    v28b10 = 717,
    v28b11 = 718,
    v28b12 = 719,
    v28b13 = 720,
    v28b14 = 721,
    v28b15 = 722,
    v29b0 = 723,
    v29b1 = 724,
    v29b2 = 725,
    v29b3 = 726,
    v29b4 = 727,
    v29b5 = 728,
    v29b6 = 729,
    v29b7 = 730,
    v29b8 = 731,
    v29b9 = 732,
    v29b10 = 733,
    v29b11 = 734,
    v29b12 = 735,
    v29b13 = 736,
    v29b14 = 737,
    v29b15 = 738,
    v30b0 = 739,
    v30b1 = 740,
    v30b2 = 741,
    v30b3 = 742,
    v30b4 = 743,
    v30b5 = 744,
    v30b6 = 745,
    v30b7 = 746,
    v30b8 = 747,
    v30b9 = 748,
    v30b10 = 749,
    v30b11 = 750,
    v30b12 = 751,
    v30b13 = 752,
    v30b14 = 753,
    v30b15 = 754,
    v31b0 = 755,
    v31b1 = 756,
    v31b2 = 757,
    v31b3 = 758,
    v31b4 = 759,
    v31b5 = 760,
    v31b6 = 761,
    v31b7 = 762,
    v31b8 = 763,
    v31b9 = 764,
    v31b10 = 765,
    v31b11 = 766,
    v31b12 = 767,
    v31b13 = 768,
    v31b14 = 769,
    v31b15 = 770,
    v0h0 = 771,
    v0h1 = 772,
    v0h2 = 773,
    v0h3 = 774,
    v0h4 = 775,
    v0h5 = 776,
    v0h6 = 777,
    v0h7 = 778,
    v1h0 = 779,
    v1h1 = 780,
    v1h2 = 781,
    v1h3 = 782,
    v1h4 = 783,
    v1h5 = 784,
    v1h6 = 785,
    v1h7 = 786,
    v2h0 = 787,
    v2h1 = 788,
    v2h2 = 789,
    v2h3 = 790,
    v2h4 = 791,
    v2h5 = 792,
    v2h6 = 793,
    v2h7 = 794,
    v3h0 = 795,
    v3h1 = 796,
    v3h2 = 797,
    v3h3 = 798,
    v3h4 = 799,
    v3h5 = 800,
    v3h6 = 801,
    v3h7 = 802,
    v4h0 = 803,
    v4h1 = 804,
    v4h2 = 805,
    v4h3 = 806,
    v4h4 = 807,
    v4h5 = 808,
    v4h6 = 809,
    v4h7 = 810,
    v5h0 = 811,
    v5h1 = 812,
    v5h2 = 813,
    v5h3 = 814,
    v5h4 = 815,
    v5h5 = 816,
    v5h6 = 817,
    v5h7 = 818,
    v6h0 = 819,
    v6h1 = 820,
    v6h2 = 821,
    v6h3 = 822,
    v6h4 = 823,
    v6h5 = 824,
    v6h6 = 825,
    v6h7 = 826,
    v7h0 = 827,
    v7h1 = 828,
    v7h2 = 829,
    v7h3 = 830,
    v7h4 = 831,
    v7h5 = 832,
    v7h6 = 833,
    v7h7 = 834,
    v8h0 = 835,
    v8h1 = 836,
    v8h2 = 837,
    v8h3 = 838,
    v8h4 = 839,
    v8h5 = 840,
    v8h6 = 841,
    v8h7 = 842,
    v9h0 = 843,
    v9h1 = 844,
    v9h2 = 845,
    v9h3 = 846,
    v9h4 = 847,
    v9h5 = 848,
    v9h6 = 849,
    v9h7 = 850,
    v10h0 = 851,
    v10h1 = 852,
    v10h2 = 853,
    v10h3 = 854,
    v10h4 = 855,
    v10h5 = 856,
    v10h6 = 857,
    v10h7 = 858,
    v11h0 = 859,
    v11h1 = 860,
    v11h2 = 861,
    v11h3 = 862,
    v11h4 = 863,
    v11h5 = 864,
    v11h6 = 865,
    v11h7 = 866,
    v12h0 = 867,
    v12h1 = 868,
    v12h2 = 869,
    v12h3 = 870,
    v12h4 = 871,
    v12h5 = 872,
    v12h6 = 873,
    v12h7 = 874,
    v13h0 = 875,
    v13h1 = 876,
    v13h2 = 877,
    v13h3 = 878,
    v13h4 = 879,
    v13h5 = 880,
    v13h6 = 881,
    v13h7 = 882,
    v14h0 = 883,
    v14h1 = 884,
    v14h2 = 885,
    v14h3 = 886,
    v14h4 = 887,
    v14h5 = 888,
    v14h6 = 889,
    v14h7 = 890,
    v15h0 = 891,
    v15h1 = 892,
    v15h2 = 893,
    v15h3 = 894,
    v15h4 = 895,
    v15h5 = 896,
    v15h6 = 897,
    v15h7 = 898,
    v16h0 = 899,
    v16h1 = 900,
    v16h2 = 901,
    v16h3 = 902,
    v16h4 = 903,
    v16h5 = 904,
    v16h6 = 905,
    v16h7 = 906,
    v17h0 = 907,
    v17h1 = 908,
    v17h2 = 909,
    v17h3 = 910,
    v17h4 = 911,
    v17h5 = 912,
    v17h6 = 913,
    v17h7 = 914,
    v18h0 = 915,
    v18h1 = 916,
    v18h2 = 917,
    v18h3 = 918,
    v18h4 = 919,
    v18h5 = 920,
    v18h6 = 921,
    v18h7 = 922,
    v19h0 = 923,
    v19h1 = 924,
    v19h2 = 925,
    v19h3 = 926,
    v19h4 = 927,
    v19h5 = 928,
    v19h6 = 929,
    v19h7 = 930,
    v20h0 = 931,
    v20h1 = 932,
    v20h2 = 933,
    v20h3 = 934,
    v20h4 = 935,
    v20h5 = 936,
    v20h6 = 937,
    v20h7 = 938,
    v21h0 = 939,
    v21h1 = 940,
    v21h2 = 941,
    v21h3 = 942,
    v21h4 = 943,
    v21h5 = 944,
    v21h6 = 945,
    v21h7 = 946,
    v22h0 = 947,
    v22h1 = 948,
    v22h2 = 949,
    v22h3 = 950,
    v22h4 = 951,
    v22h5 = 952,
    v22h6 = 953,
    v22h7 = 954,
    v23h0 = 955,
    v23h1 = 956,
    v23h2 = 957,
    v23h3 = 958,
    v23h4 = 959,
    v23h5 = 960,
    v23h6 = 961,
    v23h7 = 962,
    v24h0 = 963,
    v24h1 = 964,
    v24h2 = 965,
    v24h3 = 966,
    v24h4 = 967,
    v24h5 = 968,
    v24h6 = 969,
    v24h7 = 970,
    v25h0 = 971,
    v25h1 = 972,
    v25h2 = 973,
    v25h3 = 974,
    v25h4 = 975,
    v25h5 = 976,
    v25h6 = 977,
    v25h7 = 978,
    v26h0 = 979,
    v26h1 = 980,
    v26h2 = 981,
    v26h3 = 982,
    v26h4 = 983,
    v26h5 = 984,
    v26h6 = 985,
    v26h7 = 986,
    v27h0 = 987,
    v27h1 = 988,
    v27h2 = 989,
    v27h3 = 990,
    v27h4 = 991,
    v27h5 = 992,
    v27h6 = 993,
    v27h7 = 994,
    v28h0 = 995,
    v28h1 = 996,
    v28h2 = 997,
    v28h3 = 998,
    v28h4 = 999,
    v28h5 = 1000,
    v28h6 = 1001,
    v28h7 = 1002,
    v29h0 = 1003,
    v29h1 = 1004,
    v29h2 = 1005,
    v29h3 = 1006,
    v29h4 = 1007,
    v29h5 = 1008,
    v29h6 = 1009,
    v29h7 = 1010,
    v30h0 = 1011,
    v30h1 = 1012,
    v30h2 = 1013,
    v30h3 = 1014,
    v30h4 = 1015,
    v30h5 = 1016,
    v30h6 = 1017,
    v30h7 = 1018,
    v31h0 = 1019,
    v31h1 = 1020,
    v31h2 = 1021,
    v31h3 = 1022,
    v31h4 = 1023,
    v31h5 = 1024,
    v31h6 = 1025,
    v31h7 = 1026,
    v0s0 = 1027,
    v0s1 = 1028,
    v0s2 = 1029,
    v0s3 = 1030,
    v1s0 = 1031,
    v1s1 = 1032,
    v1s2 = 1033,
    v1s3 = 1034,
    v2s0 = 1035,
    v2s1 = 1036,
    v2s2 = 1037,
    v2s3 = 1038,
    v3s0 = 1039,
    v3s1 = 1040,
    v3s2 = 1041,
    v3s3 = 1042,
    v4s0 = 1043,
    v4s1 = 1044,
    v4s2 = 1045,
    v4s3 = 1046,
    v5s0 = 1047,
    v5s1 = 1048,
    v5s2 = 1049,
    v5s3 = 1050,
    v6s0 = 1051,
    v6s1 = 1052,
    v6s2 = 1053,
    v6s3 = 1054,
    v7s0 = 1055,
    v7s1 = 1056,
    v7s2 = 1057,
    v7s3 = 1058,
    v8s0 = 1059,
    v8s1 = 1060,
    v8s2 = 1061,
    v8s3 = 1062,
    v9s0 = 1063,
    v9s1 = 1064,
    v9s2 = 1065,
    v9s3 = 1066,
    v10s0 = 1067,
    v10s1 = 1068,
    v10s2 = 1069,
    v10s3 = 1070,
    v11s0 = 1071,
    v11s1 = 1072,
    v11s2 = 1073,
    v11s3 = 1074,
    v12s0 = 1075,
    v12s1 = 1076,
    v12s2 = 1077,
    v12s3 = 1078,
    v13s0 = 1079,
    v13s1 = 1080,
    v13s2 = 1081,
    v13s3 = 1082,
    v14s0 = 1083,
    v14s1 = 1084,
    v14s2 = 1085,
    v14s3 = 1086,
    v15s0 = 1087,
    v15s1 = 1088,
    v15s2 = 1089,
    v15s3 = 1090,
    v16s0 = 1091,
    v16s1 = 1092,
    v16s2 = 1093,
    v16s3 = 1094,
    v17s0 = 1095,
    v17s1 = 1096,
    v17s2 = 1097,
    v17s3 = 1098,
    v18s0 = 1099,
    v18s1 = 1100,
    v18s2 = 1101,
    v18s3 = 1102,
    v19s0 = 1103,
    v19s1 = 1104,
    v19s2 = 1105,
    v19s3 = 1106,
    v20s0 = 1107,
    v20s1 = 1108,
    v20s2 = 1109,
    v20s3 = 1110,
    v21s0 = 1111,
    v21s1 = 1112,
    v21s2 = 1113,
    v21s3 = 1114,
    v22s0 = 1115,
    v22s1 = 1116,
    v22s2 = 1117,
    v22s3 = 1118,
    v23s0 = 1119,
    v23s1 = 1120,
    v23s2 = 1121,
    v23s3 = 1122,
    v24s0 = 1123,
    v24s1 = 1124,
    v24s2 = 1125,
    v24s3 = 1126,
    v25s0 = 1127,
    v25s1 = 1128,
    v25s2 = 1129,
    v25s3 = 1130,
    v26s0 = 1131,
    v26s1 = 1132,
    v26s2 = 1133,
    v26s3 = 1134,
    v27s0 = 1135,
    v27s1 = 1136,
    v27s2 = 1137,
    v27s3 = 1138,
    v28s0 = 1139,
    v28s1 = 1140,
    v28s2 = 1141,
    v28s3 = 1142,
    v29s0 = 1143,
    v29s1 = 1144,
    v29s2 = 1145,
    v29s3 = 1146,
    v30s0 = 1147,
    v30s1 = 1148,
    v30s2 = 1149,
    v30s3 = 1150,
    v31s0 = 1151,
    v31s1 = 1152,
    v31s2 = 1153,
    v31s3 = 1154,
    v0d0 = 1155,
    v0d1 = 1156,
    v1d0 = 1157,
    v1d1 = 1158,
    v2d0 = 1159,
    v2d1 = 1160,
    v3d0 = 1161,
    v3d1 = 1162,
    v4d0 = 1163,
    v4d1 = 1164,
    v5d0 = 1165,
    v5d1 = 1166,
    v6d0 = 1167,
    v6d1 = 1168,
    v7d0 = 1169,
    v7d1 = 1170,
    v8d0 = 1171,
    v8d1 = 1172,
    v9d0 = 1173,
    v9d1 = 1174,
    v10d0 = 1175,
    v10d1 = 1176,
    v11d0 = 1177,
    v11d1 = 1178,
    v12d0 = 1179,
    v12d1 = 1180,
    v13d0 = 1181,
    v13d1 = 1182,
    v14d0 = 1183,
    v14d1 = 1184,
    v15d0 = 1185,
    v15d1 = 1186,
    v16d0 = 1187,
    v16d1 = 1188,
    v17d0 = 1189,
    v17d1 = 1190,
    v18d0 = 1191,
    v18d1 = 1192,
    v19d0 = 1193,
    v19d1 = 1194,
    v20d0 = 1195,
    v20d1 = 1196,
    v21d0 = 1197,
    v21d1 = 1198,
    v22d0 = 1199,
    v22d1 = 1200,
    v23d0 = 1201,
    v23d1 = 1202,
    v24d0 = 1203,
    v24d1 = 1204,
    v25d0 = 1205,
    v25d1 = 1206,
    v26d0 = 1207,
    v26d1 = 1208,
    v27d0 = 1209,
    v27d1 = 1210,
    v28d0 = 1211,
    v28d1 = 1212,
    v29d0 = 1213,
    v29d1 = 1214,
    v30d0 = 1215,
    v30d1 = 1216,
    v31d0 = 1217,
    v31d1 = 1218,
    // This is some binary ninja specific thing I think.
    syscall_info = 65534,
}

impl Arm64Reg {
    /// Size of the register in bytes.
    pub fn size(&self) -> usize {
        match self {
            Arm64Reg::w0 => 4,
            Arm64Reg::w1 => 4,
            Arm64Reg::w2 => 4,
            Arm64Reg::w3 => 4,
            Arm64Reg::w4 => 4,
            Arm64Reg::w5 => 4,
            Arm64Reg::w6 => 4,
            Arm64Reg::w7 => 4,
            Arm64Reg::w8 => 4,
            Arm64Reg::w9 => 4,
            Arm64Reg::w10 => 4,
            Arm64Reg::w11 => 4,
            Arm64Reg::w12 => 4,
            Arm64Reg::w13 => 4,
            Arm64Reg::w14 => 4,
            Arm64Reg::w15 => 4,
            Arm64Reg::w16 => 4,
            Arm64Reg::w17 => 4,
            Arm64Reg::w18 => 4,
            Arm64Reg::w19 => 4,
            Arm64Reg::w20 => 4,
            Arm64Reg::w21 => 4,
            Arm64Reg::w22 => 4,
            Arm64Reg::w23 => 4,
            Arm64Reg::w24 => 4,
            Arm64Reg::w25 => 4,
            Arm64Reg::w26 => 4,
            Arm64Reg::w27 => 4,
            Arm64Reg::w28 => 4,
            Arm64Reg::w29 => 4,
            Arm64Reg::w30 => 4,
            Arm64Reg::wsp => 4,
            Arm64Reg::x0 => 8,
            Arm64Reg::x1 => 8,
            Arm64Reg::x2 => 8,
            Arm64Reg::x3 => 8,
            Arm64Reg::x4 => 8,
            Arm64Reg::x5 => 8,
            Arm64Reg::x6 => 8,
            Arm64Reg::x7 => 8,
            Arm64Reg::x8 => 8,
            Arm64Reg::x9 => 8,
            Arm64Reg::x10 => 8,
            Arm64Reg::x11 => 8,
            Arm64Reg::x12 => 8,
            Arm64Reg::x13 => 8,
            Arm64Reg::x14 => 8,
            Arm64Reg::x15 => 8,
            Arm64Reg::x16 => 8,
            Arm64Reg::x17 => 8,
            Arm64Reg::x18 => 8,
            Arm64Reg::x19 => 8,
            Arm64Reg::x20 => 8,
            Arm64Reg::x21 => 8,
            Arm64Reg::x22 => 8,
            Arm64Reg::x23 => 8,
            Arm64Reg::x24 => 8,
            Arm64Reg::x25 => 8,
            Arm64Reg::x26 => 8,
            Arm64Reg::x27 => 8,
            Arm64Reg::x28 => 8,
            Arm64Reg::fp => 8,
            Arm64Reg::lr => 8,
            Arm64Reg::sp => 8,
            Arm64Reg::syscall_info => 8,
            Arm64Reg::d0 => 8,
            Arm64Reg::d1 => 8,
            Arm64Reg::d2 => 8,
            Arm64Reg::d3 => 8,
            Arm64Reg::d4 => 8,
            Arm64Reg::d5 => 8,
            Arm64Reg::d6 => 8,
            Arm64Reg::d7 => 8,
            Arm64Reg::d8 => 8,
            Arm64Reg::d9 => 8,
            Arm64Reg::d10 => 8,
            Arm64Reg::d11 => 8,
            Arm64Reg::d12 => 8,
            Arm64Reg::d13 => 8,
            Arm64Reg::d14 => 8,
            Arm64Reg::d15 => 8,
            Arm64Reg::d16 => 8,
            Arm64Reg::d17 => 8,
            Arm64Reg::d18 => 8,
            Arm64Reg::d19 => 8,
            Arm64Reg::d20 => 8,
            Arm64Reg::d21 => 8,
            Arm64Reg::d22 => 8,
            Arm64Reg::d23 => 8,
            Arm64Reg::d24 => 8,
            Arm64Reg::d25 => 8,
            Arm64Reg::d26 => 8,
            Arm64Reg::d27 => 8,
            Arm64Reg::d28 => 8,
            Arm64Reg::d29 => 8,
            Arm64Reg::d30 => 8,
            Arm64Reg::d31 => 8,
            Arm64Reg::s0 => 4,
            Arm64Reg::s1 => 4,
            Arm64Reg::s2 => 4,
            Arm64Reg::s3 => 4,
            Arm64Reg::s4 => 4,
            Arm64Reg::s5 => 4,
            Arm64Reg::s6 => 4,
            Arm64Reg::s7 => 4,
            Arm64Reg::s8 => 4,
            Arm64Reg::s9 => 4,
            Arm64Reg::s10 => 4,
            Arm64Reg::s11 => 4,
            Arm64Reg::s12 => 4,
            Arm64Reg::s13 => 4,
            Arm64Reg::s14 => 4,
            Arm64Reg::s15 => 4,
            Arm64Reg::s16 => 4,
            Arm64Reg::s17 => 4,
            Arm64Reg::s18 => 4,
            Arm64Reg::s19 => 4,
            Arm64Reg::s20 => 4,
            Arm64Reg::s21 => 4,
            Arm64Reg::s22 => 4,
            Arm64Reg::s23 => 4,
            Arm64Reg::s24 => 4,
            Arm64Reg::s25 => 4,
            Arm64Reg::s26 => 4,
            Arm64Reg::s27 => 4,
            Arm64Reg::s28 => 4,
            Arm64Reg::s29 => 4,
            Arm64Reg::s30 => 4,
            Arm64Reg::s31 => 4,
            Arm64Reg::q0 => 16,
            Arm64Reg::q1 => 16,
            Arm64Reg::q2 => 16,
            Arm64Reg::q3 => 16,
            Arm64Reg::q4 => 16,
            Arm64Reg::q5 => 16,
            Arm64Reg::q6 => 16,
            Arm64Reg::q7 => 16,
            Arm64Reg::q8 => 16,
            Arm64Reg::q9 => 16,
            Arm64Reg::q10 => 16,
            Arm64Reg::q11 => 16,
            Arm64Reg::q12 => 16,
            Arm64Reg::q13 => 16,
            Arm64Reg::q14 => 16,
            Arm64Reg::q15 => 16,
            Arm64Reg::q16 => 16,
            Arm64Reg::q17 => 16,
            Arm64Reg::q18 => 16,
            Arm64Reg::q19 => 16,
            Arm64Reg::q20 => 16,
            Arm64Reg::q21 => 16,
            Arm64Reg::q22 => 16,
            Arm64Reg::q23 => 16,
            Arm64Reg::q24 => 16,
            Arm64Reg::q25 => 16,
            Arm64Reg::q26 => 16,
            Arm64Reg::q27 => 16,
            Arm64Reg::q28 => 16,
            Arm64Reg::q29 => 16,
            Arm64Reg::q30 => 16,
            Arm64Reg::q31 => 16,
            Arm64Reg::v0b0 => 8,
            Arm64Reg::v0b1 => 8,
            Arm64Reg::v0b2 => 8,
            Arm64Reg::v0b3 => 8,
            Arm64Reg::v0b4 => 8,
            Arm64Reg::v0b5 => 8,
            Arm64Reg::v0b6 => 8,
            Arm64Reg::v0b7 => 8,
            Arm64Reg::v0b8 => 8,
            Arm64Reg::v0b9 => 8,
            Arm64Reg::v0b10 => 8,
            Arm64Reg::v0b11 => 8,
            Arm64Reg::v0b12 => 8,
            Arm64Reg::v0b13 => 8,
            Arm64Reg::v0b14 => 8,
            Arm64Reg::v0b15 => 8,
            Arm64Reg::v1b0 => 8,
            Arm64Reg::v1b1 => 8,
            Arm64Reg::v1b2 => 8,
            Arm64Reg::v1b3 => 8,
            Arm64Reg::v1b4 => 8,
            Arm64Reg::v1b5 => 8,
            Arm64Reg::v1b6 => 8,
            Arm64Reg::v1b7 => 8,
            Arm64Reg::v1b8 => 8,
            Arm64Reg::v1b9 => 8,
            Arm64Reg::v1b10 => 8,
            Arm64Reg::v1b11 => 8,
            Arm64Reg::v1b12 => 8,
            Arm64Reg::v1b13 => 8,
            Arm64Reg::v1b14 => 8,
            Arm64Reg::v1b15 => 8,
            Arm64Reg::v2b0 => 8,
            Arm64Reg::v2b1 => 8,
            Arm64Reg::v2b2 => 8,
            Arm64Reg::v2b3 => 8,
            Arm64Reg::v2b4 => 8,
            Arm64Reg::v2b5 => 8,
            Arm64Reg::v2b6 => 8,
            Arm64Reg::v2b7 => 8,
            Arm64Reg::v2b8 => 8,
            Arm64Reg::v2b9 => 8,
            Arm64Reg::v2b10 => 8,
            Arm64Reg::v2b11 => 8,
            Arm64Reg::v2b12 => 8,
            Arm64Reg::v2b13 => 8,
            Arm64Reg::v2b14 => 8,
            Arm64Reg::v2b15 => 8,
            Arm64Reg::v3b0 => 8,
            Arm64Reg::v3b1 => 8,
            Arm64Reg::v3b2 => 8,
            Arm64Reg::v3b3 => 8,
            Arm64Reg::v3b4 => 8,
            Arm64Reg::v3b5 => 8,
            Arm64Reg::v3b6 => 8,
            Arm64Reg::v3b7 => 8,
            Arm64Reg::v3b8 => 8,
            Arm64Reg::v3b9 => 8,
            Arm64Reg::v3b10 => 8,
            Arm64Reg::v3b11 => 8,
            Arm64Reg::v3b12 => 8,
            Arm64Reg::v3b13 => 8,
            Arm64Reg::v3b14 => 8,
            Arm64Reg::v3b15 => 8,
            Arm64Reg::v4b0 => 8,
            Arm64Reg::v4b1 => 8,
            Arm64Reg::v4b2 => 8,
            Arm64Reg::v4b3 => 8,
            Arm64Reg::v4b4 => 8,
            Arm64Reg::v4b5 => 8,
            Arm64Reg::v4b6 => 8,
            Arm64Reg::v4b7 => 8,
            Arm64Reg::v4b8 => 8,
            Arm64Reg::v4b9 => 8,
            Arm64Reg::v4b10 => 8,
            Arm64Reg::v4b11 => 8,
            Arm64Reg::v4b12 => 8,
            Arm64Reg::v4b13 => 8,
            Arm64Reg::v4b14 => 8,
            Arm64Reg::v4b15 => 8,
            Arm64Reg::v5b0 => 8,
            Arm64Reg::v5b1 => 8,
            Arm64Reg::v5b2 => 8,
            Arm64Reg::v5b3 => 8,
            Arm64Reg::v5b4 => 8,
            Arm64Reg::v5b5 => 8,
            Arm64Reg::v5b6 => 8,
            Arm64Reg::v5b7 => 8,
            Arm64Reg::v5b8 => 8,
            Arm64Reg::v5b9 => 8,
            Arm64Reg::v5b10 => 8,
            Arm64Reg::v5b11 => 8,
            Arm64Reg::v5b12 => 8,
            Arm64Reg::v5b13 => 8,
            Arm64Reg::v5b14 => 8,
            Arm64Reg::v5b15 => 8,
            Arm64Reg::v6b0 => 8,
            Arm64Reg::v6b1 => 8,
            Arm64Reg::v6b2 => 8,
            Arm64Reg::v6b3 => 8,
            Arm64Reg::v6b4 => 8,
            Arm64Reg::v6b5 => 8,
            Arm64Reg::v6b6 => 8,
            Arm64Reg::v6b7 => 8,
            Arm64Reg::v6b8 => 8,
            Arm64Reg::v6b9 => 8,
            Arm64Reg::v6b10 => 8,
            Arm64Reg::v6b11 => 8,
            Arm64Reg::v6b12 => 8,
            Arm64Reg::v6b13 => 8,
            Arm64Reg::v6b14 => 8,
            Arm64Reg::v6b15 => 8,
            Arm64Reg::v7b0 => 8,
            Arm64Reg::v7b1 => 8,
            Arm64Reg::v7b2 => 8,
            Arm64Reg::v7b3 => 8,
            Arm64Reg::v7b4 => 8,
            Arm64Reg::v7b5 => 8,
            Arm64Reg::v7b6 => 8,
            Arm64Reg::v7b7 => 8,
            Arm64Reg::v7b8 => 8,
            Arm64Reg::v7b9 => 8,
            Arm64Reg::v7b10 => 8,
            Arm64Reg::v7b11 => 8,
            Arm64Reg::v7b12 => 8,
            Arm64Reg::v7b13 => 8,
            Arm64Reg::v7b14 => 8,
            Arm64Reg::v7b15 => 8,
            Arm64Reg::v8b0 => 8,
            Arm64Reg::v8b1 => 8,
            Arm64Reg::v8b2 => 8,
            Arm64Reg::v8b3 => 8,
            Arm64Reg::v8b4 => 8,
            Arm64Reg::v8b5 => 8,
            Arm64Reg::v8b6 => 8,
            Arm64Reg::v8b7 => 8,
            Arm64Reg::v8b8 => 8,
            Arm64Reg::v8b9 => 8,
            Arm64Reg::v8b10 => 8,
            Arm64Reg::v8b11 => 8,
            Arm64Reg::v8b12 => 8,
            Arm64Reg::v8b13 => 8,
            Arm64Reg::v8b14 => 8,
            Arm64Reg::v8b15 => 8,
            Arm64Reg::v9b0 => 8,
            Arm64Reg::v9b1 => 8,
            Arm64Reg::v9b2 => 8,
            Arm64Reg::v9b3 => 8,
            Arm64Reg::v9b4 => 8,
            Arm64Reg::v9b5 => 8,
            Arm64Reg::v9b6 => 8,
            Arm64Reg::v9b7 => 8,
            Arm64Reg::v9b8 => 8,
            Arm64Reg::v9b9 => 8,
            Arm64Reg::v9b10 => 8,
            Arm64Reg::v9b11 => 8,
            Arm64Reg::v9b12 => 8,
            Arm64Reg::v9b13 => 8,
            Arm64Reg::v9b14 => 8,
            Arm64Reg::v9b15 => 8,
            Arm64Reg::v10b0 => 8,
            Arm64Reg::v10b1 => 8,
            Arm64Reg::v10b2 => 8,
            Arm64Reg::v10b3 => 8,
            Arm64Reg::v10b4 => 8,
            Arm64Reg::v10b5 => 8,
            Arm64Reg::v10b6 => 8,
            Arm64Reg::v10b7 => 8,
            Arm64Reg::v10b8 => 8,
            Arm64Reg::v10b9 => 8,
            Arm64Reg::v10b10 => 8,
            Arm64Reg::v10b11 => 8,
            Arm64Reg::v10b12 => 8,
            Arm64Reg::v10b13 => 8,
            Arm64Reg::v10b14 => 8,
            Arm64Reg::v10b15 => 8,
            Arm64Reg::v11b0 => 8,
            Arm64Reg::v11b1 => 8,
            Arm64Reg::v11b2 => 8,
            Arm64Reg::v11b3 => 8,
            Arm64Reg::v11b4 => 8,
            Arm64Reg::v11b5 => 8,
            Arm64Reg::v11b6 => 8,
            Arm64Reg::v11b7 => 8,
            Arm64Reg::v11b8 => 8,
            Arm64Reg::v11b9 => 8,
            Arm64Reg::v11b10 => 8,
            Arm64Reg::v11b11 => 8,
            Arm64Reg::v11b12 => 8,
            Arm64Reg::v11b13 => 8,
            Arm64Reg::v11b14 => 8,
            Arm64Reg::v11b15 => 8,
            Arm64Reg::v12b0 => 8,
            Arm64Reg::v12b1 => 8,
            Arm64Reg::v12b2 => 8,
            Arm64Reg::v12b3 => 8,
            Arm64Reg::v12b4 => 8,
            Arm64Reg::v12b5 => 8,
            Arm64Reg::v12b6 => 8,
            Arm64Reg::v12b7 => 8,
            Arm64Reg::v12b8 => 8,
            Arm64Reg::v12b9 => 8,
            Arm64Reg::v12b10 => 8,
            Arm64Reg::v12b11 => 8,
            Arm64Reg::v12b12 => 8,
            Arm64Reg::v12b13 => 8,
            Arm64Reg::v12b14 => 8,
            Arm64Reg::v12b15 => 8,
            Arm64Reg::v13b0 => 8,
            Arm64Reg::v13b1 => 8,
            Arm64Reg::v13b2 => 8,
            Arm64Reg::v13b3 => 8,
            Arm64Reg::v13b4 => 8,
            Arm64Reg::v13b5 => 8,
            Arm64Reg::v13b6 => 8,
            Arm64Reg::v13b7 => 8,
            Arm64Reg::v13b8 => 8,
            Arm64Reg::v13b9 => 8,
            Arm64Reg::v13b10 => 8,
            Arm64Reg::v13b11 => 8,
            Arm64Reg::v13b12 => 8,
            Arm64Reg::v13b13 => 8,
            Arm64Reg::v13b14 => 8,
            Arm64Reg::v13b15 => 8,
            Arm64Reg::v14b0 => 8,
            Arm64Reg::v14b1 => 8,
            Arm64Reg::v14b2 => 8,
            Arm64Reg::v14b3 => 8,
            Arm64Reg::v14b4 => 8,
            Arm64Reg::v14b5 => 8,
            Arm64Reg::v14b6 => 8,
            Arm64Reg::v14b7 => 8,
            Arm64Reg::v14b8 => 8,
            Arm64Reg::v14b9 => 8,
            Arm64Reg::v14b10 => 8,
            Arm64Reg::v14b11 => 8,
            Arm64Reg::v14b12 => 8,
            Arm64Reg::v14b13 => 8,
            Arm64Reg::v14b14 => 8,
            Arm64Reg::v14b15 => 8,
            Arm64Reg::v15b0 => 8,
            Arm64Reg::v15b1 => 8,
            Arm64Reg::v15b2 => 8,
            Arm64Reg::v15b3 => 8,
            Arm64Reg::v15b4 => 8,
            Arm64Reg::v15b5 => 8,
            Arm64Reg::v15b6 => 8,
            Arm64Reg::v15b7 => 8,
            Arm64Reg::v15b8 => 8,
            Arm64Reg::v15b9 => 8,
            Arm64Reg::v15b10 => 8,
            Arm64Reg::v15b11 => 8,
            Arm64Reg::v15b12 => 8,
            Arm64Reg::v15b13 => 8,
            Arm64Reg::v15b14 => 8,
            Arm64Reg::v15b15 => 8,
            Arm64Reg::v16b0 => 8,
            Arm64Reg::v16b1 => 8,
            Arm64Reg::v16b2 => 8,
            Arm64Reg::v16b3 => 8,
            Arm64Reg::v16b4 => 8,
            Arm64Reg::v16b5 => 8,
            Arm64Reg::v16b6 => 8,
            Arm64Reg::v16b7 => 8,
            Arm64Reg::v16b8 => 8,
            Arm64Reg::v16b9 => 8,
            Arm64Reg::v16b10 => 8,
            Arm64Reg::v16b11 => 8,
            Arm64Reg::v16b12 => 8,
            Arm64Reg::v16b13 => 8,
            Arm64Reg::v16b14 => 8,
            Arm64Reg::v16b15 => 8,
            Arm64Reg::v17b0 => 8,
            Arm64Reg::v17b1 => 8,
            Arm64Reg::v17b2 => 8,
            Arm64Reg::v17b3 => 8,
            Arm64Reg::v17b4 => 8,
            Arm64Reg::v17b5 => 8,
            Arm64Reg::v17b6 => 8,
            Arm64Reg::v17b7 => 8,
            Arm64Reg::v17b8 => 8,
            Arm64Reg::v17b9 => 8,
            Arm64Reg::v17b10 => 8,
            Arm64Reg::v17b11 => 8,
            Arm64Reg::v17b12 => 8,
            Arm64Reg::v17b13 => 8,
            Arm64Reg::v17b14 => 8,
            Arm64Reg::v17b15 => 8,
            Arm64Reg::v18b0 => 8,
            Arm64Reg::v18b1 => 8,
            Arm64Reg::v18b2 => 8,
            Arm64Reg::v18b3 => 8,
            Arm64Reg::v18b4 => 8,
            Arm64Reg::v18b5 => 8,
            Arm64Reg::v18b6 => 8,
            Arm64Reg::v18b7 => 8,
            Arm64Reg::v18b8 => 8,
            Arm64Reg::v18b9 => 8,
            Arm64Reg::v18b10 => 8,
            Arm64Reg::v18b11 => 8,
            Arm64Reg::v18b12 => 8,
            Arm64Reg::v18b13 => 8,
            Arm64Reg::v18b14 => 8,
            Arm64Reg::v18b15 => 8,
            Arm64Reg::v19b0 => 8,
            Arm64Reg::v19b1 => 8,
            Arm64Reg::v19b2 => 8,
            Arm64Reg::v19b3 => 8,
            Arm64Reg::v19b4 => 8,
            Arm64Reg::v19b5 => 8,
            Arm64Reg::v19b6 => 8,
            Arm64Reg::v19b7 => 8,
            Arm64Reg::v19b8 => 8,
            Arm64Reg::v19b9 => 8,
            Arm64Reg::v19b10 => 8,
            Arm64Reg::v19b11 => 8,
            Arm64Reg::v19b12 => 8,
            Arm64Reg::v19b13 => 8,
            Arm64Reg::v19b14 => 8,
            Arm64Reg::v19b15 => 8,
            Arm64Reg::v20b0 => 8,
            Arm64Reg::v20b1 => 8,
            Arm64Reg::v20b2 => 8,
            Arm64Reg::v20b3 => 8,
            Arm64Reg::v20b4 => 8,
            Arm64Reg::v20b5 => 8,
            Arm64Reg::v20b6 => 8,
            Arm64Reg::v20b7 => 8,
            Arm64Reg::v20b8 => 8,
            Arm64Reg::v20b9 => 8,
            Arm64Reg::v20b10 => 8,
            Arm64Reg::v20b11 => 8,
            Arm64Reg::v20b12 => 8,
            Arm64Reg::v20b13 => 8,
            Arm64Reg::v20b14 => 8,
            Arm64Reg::v20b15 => 8,
            Arm64Reg::v21b0 => 8,
            Arm64Reg::v21b1 => 8,
            Arm64Reg::v21b2 => 8,
            Arm64Reg::v21b3 => 8,
            Arm64Reg::v21b4 => 8,
            Arm64Reg::v21b5 => 8,
            Arm64Reg::v21b6 => 8,
            Arm64Reg::v21b7 => 8,
            Arm64Reg::v21b8 => 8,
            Arm64Reg::v21b9 => 8,
            Arm64Reg::v21b10 => 8,
            Arm64Reg::v21b11 => 8,
            Arm64Reg::v21b12 => 8,
            Arm64Reg::v21b13 => 8,
            Arm64Reg::v21b14 => 8,
            Arm64Reg::v21b15 => 8,
            Arm64Reg::v22b0 => 8,
            Arm64Reg::v22b1 => 8,
            Arm64Reg::v22b2 => 8,
            Arm64Reg::v22b3 => 8,
            Arm64Reg::v22b4 => 8,
            Arm64Reg::v22b5 => 8,
            Arm64Reg::v22b6 => 8,
            Arm64Reg::v22b7 => 8,
            Arm64Reg::v22b8 => 8,
            Arm64Reg::v22b9 => 8,
            Arm64Reg::v22b10 => 8,
            Arm64Reg::v22b11 => 8,
            Arm64Reg::v22b12 => 8,
            Arm64Reg::v22b13 => 8,
            Arm64Reg::v22b14 => 8,
            Arm64Reg::v22b15 => 8,
            Arm64Reg::v23b0 => 8,
            Arm64Reg::v23b1 => 8,
            Arm64Reg::v23b2 => 8,
            Arm64Reg::v23b3 => 8,
            Arm64Reg::v23b4 => 8,
            Arm64Reg::v23b5 => 8,
            Arm64Reg::v23b6 => 8,
            Arm64Reg::v23b7 => 8,
            Arm64Reg::v23b8 => 8,
            Arm64Reg::v23b9 => 8,
            Arm64Reg::v23b10 => 8,
            Arm64Reg::v23b11 => 8,
            Arm64Reg::v23b12 => 8,
            Arm64Reg::v23b13 => 8,
            Arm64Reg::v23b14 => 8,
            Arm64Reg::v23b15 => 8,
            Arm64Reg::v24b0 => 8,
            Arm64Reg::v24b1 => 8,
            Arm64Reg::v24b2 => 8,
            Arm64Reg::v24b3 => 8,
            Arm64Reg::v24b4 => 8,
            Arm64Reg::v24b5 => 8,
            Arm64Reg::v24b6 => 8,
            Arm64Reg::v24b7 => 8,
            Arm64Reg::v24b8 => 8,
            Arm64Reg::v24b9 => 8,
            Arm64Reg::v24b10 => 8,
            Arm64Reg::v24b11 => 8,
            Arm64Reg::v24b12 => 8,
            Arm64Reg::v24b13 => 8,
            Arm64Reg::v24b14 => 8,
            Arm64Reg::v24b15 => 8,
            Arm64Reg::v25b0 => 8,
            Arm64Reg::v25b1 => 8,
            Arm64Reg::v25b2 => 8,
            Arm64Reg::v25b3 => 8,
            Arm64Reg::v25b4 => 8,
            Arm64Reg::v25b5 => 8,
            Arm64Reg::v25b6 => 8,
            Arm64Reg::v25b7 => 8,
            Arm64Reg::v25b8 => 8,
            Arm64Reg::v25b9 => 8,
            Arm64Reg::v25b10 => 8,
            Arm64Reg::v25b11 => 8,
            Arm64Reg::v25b12 => 8,
            Arm64Reg::v25b13 => 8,
            Arm64Reg::v25b14 => 8,
            Arm64Reg::v25b15 => 8,
            Arm64Reg::v26b0 => 8,
            Arm64Reg::v26b1 => 8,
            Arm64Reg::v26b2 => 8,
            Arm64Reg::v26b3 => 8,
            Arm64Reg::v26b4 => 8,
            Arm64Reg::v26b5 => 8,
            Arm64Reg::v26b6 => 8,
            Arm64Reg::v26b7 => 8,
            Arm64Reg::v26b8 => 8,
            Arm64Reg::v26b9 => 8,
            Arm64Reg::v26b10 => 8,
            Arm64Reg::v26b11 => 8,
            Arm64Reg::v26b12 => 8,
            Arm64Reg::v26b13 => 8,
            Arm64Reg::v26b14 => 8,
            Arm64Reg::v26b15 => 8,
            Arm64Reg::v27b0 => 8,
            Arm64Reg::v27b1 => 8,
            Arm64Reg::v27b2 => 8,
            Arm64Reg::v27b3 => 8,
            Arm64Reg::v27b4 => 8,
            Arm64Reg::v27b5 => 8,
            Arm64Reg::v27b6 => 8,
            Arm64Reg::v27b7 => 8,
            Arm64Reg::v27b8 => 8,
            Arm64Reg::v27b9 => 8,
            Arm64Reg::v27b10 => 8,
            Arm64Reg::v27b11 => 8,
            Arm64Reg::v27b12 => 8,
            Arm64Reg::v27b13 => 8,
            Arm64Reg::v27b14 => 8,
            Arm64Reg::v27b15 => 8,
            Arm64Reg::v28b0 => 8,
            Arm64Reg::v28b1 => 8,
            Arm64Reg::v28b2 => 8,
            Arm64Reg::v28b3 => 8,
            Arm64Reg::v28b4 => 8,
            Arm64Reg::v28b5 => 8,
            Arm64Reg::v28b6 => 8,
            Arm64Reg::v28b7 => 8,
            Arm64Reg::v28b8 => 8,
            Arm64Reg::v28b9 => 8,
            Arm64Reg::v28b10 => 8,
            Arm64Reg::v28b11 => 8,
            Arm64Reg::v28b12 => 8,
            Arm64Reg::v28b13 => 8,
            Arm64Reg::v28b14 => 8,
            Arm64Reg::v28b15 => 8,
            Arm64Reg::v29b0 => 8,
            Arm64Reg::v29b1 => 8,
            Arm64Reg::v29b2 => 8,
            Arm64Reg::v29b3 => 8,
            Arm64Reg::v29b4 => 8,
            Arm64Reg::v29b5 => 8,
            Arm64Reg::v29b6 => 8,
            Arm64Reg::v29b7 => 8,
            Arm64Reg::v29b8 => 8,
            Arm64Reg::v29b9 => 8,
            Arm64Reg::v29b10 => 8,
            Arm64Reg::v29b11 => 8,
            Arm64Reg::v29b12 => 8,
            Arm64Reg::v29b13 => 8,
            Arm64Reg::v29b14 => 8,
            Arm64Reg::v29b15 => 8,
            Arm64Reg::v30b0 => 8,
            Arm64Reg::v30b1 => 8,
            Arm64Reg::v30b2 => 8,
            Arm64Reg::v30b3 => 8,
            Arm64Reg::v30b4 => 8,
            Arm64Reg::v30b5 => 8,
            Arm64Reg::v30b6 => 8,
            Arm64Reg::v30b7 => 8,
            Arm64Reg::v30b8 => 8,
            Arm64Reg::v30b9 => 8,
            Arm64Reg::v30b10 => 8,
            Arm64Reg::v30b11 => 8,
            Arm64Reg::v30b12 => 8,
            Arm64Reg::v30b13 => 8,
            Arm64Reg::v30b14 => 8,
            Arm64Reg::v30b15 => 8,
            Arm64Reg::v31b0 => 8,
            Arm64Reg::v31b1 => 8,
            Arm64Reg::v31b2 => 8,
            Arm64Reg::v31b3 => 8,
            Arm64Reg::v31b4 => 8,
            Arm64Reg::v31b5 => 8,
            Arm64Reg::v31b6 => 8,
            Arm64Reg::v31b7 => 8,
            Arm64Reg::v31b8 => 8,
            Arm64Reg::v31b9 => 8,
            Arm64Reg::v31b10 => 8,
            Arm64Reg::v31b11 => 8,
            Arm64Reg::v31b12 => 8,
            Arm64Reg::v31b13 => 8,
            Arm64Reg::v31b14 => 8,
            Arm64Reg::v31b15 => 8,
            Arm64Reg::v0h0 => 16,
            Arm64Reg::v0h1 => 16,
            Arm64Reg::v0h2 => 16,
            Arm64Reg::v0h3 => 16,
            Arm64Reg::v0h4 => 16,
            Arm64Reg::v0h5 => 16,
            Arm64Reg::v0h6 => 16,
            Arm64Reg::v0h7 => 16,
            Arm64Reg::v1h0 => 16,
            Arm64Reg::v1h1 => 16,
            Arm64Reg::v1h2 => 16,
            Arm64Reg::v1h3 => 16,
            Arm64Reg::v1h4 => 16,
            Arm64Reg::v1h5 => 16,
            Arm64Reg::v1h6 => 16,
            Arm64Reg::v1h7 => 16,
            Arm64Reg::v2h0 => 16,
            Arm64Reg::v2h1 => 16,
            Arm64Reg::v2h2 => 16,
            Arm64Reg::v2h3 => 16,
            Arm64Reg::v2h4 => 16,
            Arm64Reg::v2h5 => 16,
            Arm64Reg::v2h6 => 16,
            Arm64Reg::v2h7 => 16,
            Arm64Reg::v3h0 => 16,
            Arm64Reg::v3h1 => 16,
            Arm64Reg::v3h2 => 16,
            Arm64Reg::v3h3 => 16,
            Arm64Reg::v3h4 => 16,
            Arm64Reg::v3h5 => 16,
            Arm64Reg::v3h6 => 16,
            Arm64Reg::v3h7 => 16,
            Arm64Reg::v4h0 => 16,
            Arm64Reg::v4h1 => 16,
            Arm64Reg::v4h2 => 16,
            Arm64Reg::v4h3 => 16,
            Arm64Reg::v4h4 => 16,
            Arm64Reg::v4h5 => 16,
            Arm64Reg::v4h6 => 16,
            Arm64Reg::v4h7 => 16,
            Arm64Reg::v5h0 => 16,
            Arm64Reg::v5h1 => 16,
            Arm64Reg::v5h2 => 16,
            Arm64Reg::v5h3 => 16,
            Arm64Reg::v5h4 => 16,
            Arm64Reg::v5h5 => 16,
            Arm64Reg::v5h6 => 16,
            Arm64Reg::v5h7 => 16,
            Arm64Reg::v6h0 => 16,
            Arm64Reg::v6h1 => 16,
            Arm64Reg::v6h2 => 16,
            Arm64Reg::v6h3 => 16,
            Arm64Reg::v6h4 => 16,
            Arm64Reg::v6h5 => 16,
            Arm64Reg::v6h6 => 16,
            Arm64Reg::v6h7 => 16,
            Arm64Reg::v7h0 => 16,
            Arm64Reg::v7h1 => 16,
            Arm64Reg::v7h2 => 16,
            Arm64Reg::v7h3 => 16,
            Arm64Reg::v7h4 => 16,
            Arm64Reg::v7h5 => 16,
            Arm64Reg::v7h6 => 16,
            Arm64Reg::v7h7 => 16,
            Arm64Reg::v8h0 => 16,
            Arm64Reg::v8h1 => 16,
            Arm64Reg::v8h2 => 16,
            Arm64Reg::v8h3 => 16,
            Arm64Reg::v8h4 => 16,
            Arm64Reg::v8h5 => 16,
            Arm64Reg::v8h6 => 16,
            Arm64Reg::v8h7 => 16,
            Arm64Reg::v9h0 => 16,
            Arm64Reg::v9h1 => 16,
            Arm64Reg::v9h2 => 16,
            Arm64Reg::v9h3 => 16,
            Arm64Reg::v9h4 => 16,
            Arm64Reg::v9h5 => 16,
            Arm64Reg::v9h6 => 16,
            Arm64Reg::v9h7 => 16,
            Arm64Reg::v10h0 => 16,
            Arm64Reg::v10h1 => 16,
            Arm64Reg::v10h2 => 16,
            Arm64Reg::v10h3 => 16,
            Arm64Reg::v10h4 => 16,
            Arm64Reg::v10h5 => 16,
            Arm64Reg::v10h6 => 16,
            Arm64Reg::v10h7 => 16,
            Arm64Reg::v11h0 => 16,
            Arm64Reg::v11h1 => 16,
            Arm64Reg::v11h2 => 16,
            Arm64Reg::v11h3 => 16,
            Arm64Reg::v11h4 => 16,
            Arm64Reg::v11h5 => 16,
            Arm64Reg::v11h6 => 16,
            Arm64Reg::v11h7 => 16,
            Arm64Reg::v12h0 => 16,
            Arm64Reg::v12h1 => 16,
            Arm64Reg::v12h2 => 16,
            Arm64Reg::v12h3 => 16,
            Arm64Reg::v12h4 => 16,
            Arm64Reg::v12h5 => 16,
            Arm64Reg::v12h6 => 16,
            Arm64Reg::v12h7 => 16,
            Arm64Reg::v13h0 => 16,
            Arm64Reg::v13h1 => 16,
            Arm64Reg::v13h2 => 16,
            Arm64Reg::v13h3 => 16,
            Arm64Reg::v13h4 => 16,
            Arm64Reg::v13h5 => 16,
            Arm64Reg::v13h6 => 16,
            Arm64Reg::v13h7 => 16,
            Arm64Reg::v14h0 => 16,
            Arm64Reg::v14h1 => 16,
            Arm64Reg::v14h2 => 16,
            Arm64Reg::v14h3 => 16,
            Arm64Reg::v14h4 => 16,
            Arm64Reg::v14h5 => 16,
            Arm64Reg::v14h6 => 16,
            Arm64Reg::v14h7 => 16,
            Arm64Reg::v15h0 => 16,
            Arm64Reg::v15h1 => 16,
            Arm64Reg::v15h2 => 16,
            Arm64Reg::v15h3 => 16,
            Arm64Reg::v15h4 => 16,
            Arm64Reg::v15h5 => 16,
            Arm64Reg::v15h6 => 16,
            Arm64Reg::v15h7 => 16,
            Arm64Reg::v16h0 => 16,
            Arm64Reg::v16h1 => 16,
            Arm64Reg::v16h2 => 16,
            Arm64Reg::v16h3 => 16,
            Arm64Reg::v16h4 => 16,
            Arm64Reg::v16h5 => 16,
            Arm64Reg::v16h6 => 16,
            Arm64Reg::v16h7 => 16,
            Arm64Reg::v17h0 => 16,
            Arm64Reg::v17h1 => 16,
            Arm64Reg::v17h2 => 16,
            Arm64Reg::v17h3 => 16,
            Arm64Reg::v17h4 => 16,
            Arm64Reg::v17h5 => 16,
            Arm64Reg::v17h6 => 16,
            Arm64Reg::v17h7 => 16,
            Arm64Reg::v18h0 => 16,
            Arm64Reg::v18h1 => 16,
            Arm64Reg::v18h2 => 16,
            Arm64Reg::v18h3 => 16,
            Arm64Reg::v18h4 => 16,
            Arm64Reg::v18h5 => 16,
            Arm64Reg::v18h6 => 16,
            Arm64Reg::v18h7 => 16,
            Arm64Reg::v19h0 => 16,
            Arm64Reg::v19h1 => 16,
            Arm64Reg::v19h2 => 16,
            Arm64Reg::v19h3 => 16,
            Arm64Reg::v19h4 => 16,
            Arm64Reg::v19h5 => 16,
            Arm64Reg::v19h6 => 16,
            Arm64Reg::v19h7 => 16,
            Arm64Reg::v20h0 => 16,
            Arm64Reg::v20h1 => 16,
            Arm64Reg::v20h2 => 16,
            Arm64Reg::v20h3 => 16,
            Arm64Reg::v20h4 => 16,
            Arm64Reg::v20h5 => 16,
            Arm64Reg::v20h6 => 16,
            Arm64Reg::v20h7 => 16,
            Arm64Reg::v21h0 => 16,
            Arm64Reg::v21h1 => 16,
            Arm64Reg::v21h2 => 16,
            Arm64Reg::v21h3 => 16,
            Arm64Reg::v21h4 => 16,
            Arm64Reg::v21h5 => 16,
            Arm64Reg::v21h6 => 16,
            Arm64Reg::v21h7 => 16,
            Arm64Reg::v22h0 => 16,
            Arm64Reg::v22h1 => 16,
            Arm64Reg::v22h2 => 16,
            Arm64Reg::v22h3 => 16,
            Arm64Reg::v22h4 => 16,
            Arm64Reg::v22h5 => 16,
            Arm64Reg::v22h6 => 16,
            Arm64Reg::v22h7 => 16,
            Arm64Reg::v23h0 => 16,
            Arm64Reg::v23h1 => 16,
            Arm64Reg::v23h2 => 16,
            Arm64Reg::v23h3 => 16,
            Arm64Reg::v23h4 => 16,
            Arm64Reg::v23h5 => 16,
            Arm64Reg::v23h6 => 16,
            Arm64Reg::v23h7 => 16,
            Arm64Reg::v24h0 => 16,
            Arm64Reg::v24h1 => 16,
            Arm64Reg::v24h2 => 16,
            Arm64Reg::v24h3 => 16,
            Arm64Reg::v24h4 => 16,
            Arm64Reg::v24h5 => 16,
            Arm64Reg::v24h6 => 16,
            Arm64Reg::v24h7 => 16,
            Arm64Reg::v25h0 => 16,
            Arm64Reg::v25h1 => 16,
            Arm64Reg::v25h2 => 16,
            Arm64Reg::v25h3 => 16,
            Arm64Reg::v25h4 => 16,
            Arm64Reg::v25h5 => 16,
            Arm64Reg::v25h6 => 16,
            Arm64Reg::v25h7 => 16,
            Arm64Reg::v26h0 => 16,
            Arm64Reg::v26h1 => 16,
            Arm64Reg::v26h2 => 16,
            Arm64Reg::v26h3 => 16,
            Arm64Reg::v26h4 => 16,
            Arm64Reg::v26h5 => 16,
            Arm64Reg::v26h6 => 16,
            Arm64Reg::v26h7 => 16,
            Arm64Reg::v27h0 => 16,
            Arm64Reg::v27h1 => 16,
            Arm64Reg::v27h2 => 16,
            Arm64Reg::v27h3 => 16,
            Arm64Reg::v27h4 => 16,
            Arm64Reg::v27h5 => 16,
            Arm64Reg::v27h6 => 16,
            Arm64Reg::v27h7 => 16,
            Arm64Reg::v28h0 => 16,
            Arm64Reg::v28h1 => 16,
            Arm64Reg::v28h2 => 16,
            Arm64Reg::v28h3 => 16,
            Arm64Reg::v28h4 => 16,
            Arm64Reg::v28h5 => 16,
            Arm64Reg::v28h6 => 16,
            Arm64Reg::v28h7 => 16,
            Arm64Reg::v29h0 => 16,
            Arm64Reg::v29h1 => 16,
            Arm64Reg::v29h2 => 16,
            Arm64Reg::v29h3 => 16,
            Arm64Reg::v29h4 => 16,
            Arm64Reg::v29h5 => 16,
            Arm64Reg::v29h6 => 16,
            Arm64Reg::v29h7 => 16,
            Arm64Reg::v30h0 => 16,
            Arm64Reg::v30h1 => 16,
            Arm64Reg::v30h2 => 16,
            Arm64Reg::v30h3 => 16,
            Arm64Reg::v30h4 => 16,
            Arm64Reg::v30h5 => 16,
            Arm64Reg::v30h6 => 16,
            Arm64Reg::v30h7 => 16,
            Arm64Reg::v31h0 => 16,
            Arm64Reg::v31h1 => 16,
            Arm64Reg::v31h2 => 16,
            Arm64Reg::v31h3 => 16,
            Arm64Reg::v31h4 => 16,
            Arm64Reg::v31h5 => 16,
            Arm64Reg::v31h6 => 16,
            Arm64Reg::v31h7 => 16,
            Arm64Reg::v0s0 => 32,
            Arm64Reg::v0s1 => 32,
            Arm64Reg::v0s2 => 32,
            Arm64Reg::v0s3 => 32,
            Arm64Reg::v1s0 => 32,
            Arm64Reg::v1s1 => 32,
            Arm64Reg::v1s2 => 32,
            Arm64Reg::v1s3 => 32,
            Arm64Reg::v2s0 => 32,
            Arm64Reg::v2s1 => 32,
            Arm64Reg::v2s2 => 32,
            Arm64Reg::v2s3 => 32,
            Arm64Reg::v3s0 => 32,
            Arm64Reg::v3s1 => 32,
            Arm64Reg::v3s2 => 32,
            Arm64Reg::v3s3 => 32,
            Arm64Reg::v4s0 => 32,
            Arm64Reg::v4s1 => 32,
            Arm64Reg::v4s2 => 32,
            Arm64Reg::v4s3 => 32,
            Arm64Reg::v5s0 => 32,
            Arm64Reg::v5s1 => 32,
            Arm64Reg::v5s2 => 32,
            Arm64Reg::v5s3 => 32,
            Arm64Reg::v6s0 => 32,
            Arm64Reg::v6s1 => 32,
            Arm64Reg::v6s2 => 32,
            Arm64Reg::v6s3 => 32,
            Arm64Reg::v7s0 => 32,
            Arm64Reg::v7s1 => 32,
            Arm64Reg::v7s2 => 32,
            Arm64Reg::v7s3 => 32,
            Arm64Reg::v8s0 => 32,
            Arm64Reg::v8s1 => 32,
            Arm64Reg::v8s2 => 32,
            Arm64Reg::v8s3 => 32,
            Arm64Reg::v9s0 => 32,
            Arm64Reg::v9s1 => 32,
            Arm64Reg::v9s2 => 32,
            Arm64Reg::v9s3 => 32,
            Arm64Reg::v10s0 => 32,
            Arm64Reg::v10s1 => 32,
            Arm64Reg::v10s2 => 32,
            Arm64Reg::v10s3 => 32,
            Arm64Reg::v11s0 => 32,
            Arm64Reg::v11s1 => 32,
            Arm64Reg::v11s2 => 32,
            Arm64Reg::v11s3 => 32,
            Arm64Reg::v12s0 => 32,
            Arm64Reg::v12s1 => 32,
            Arm64Reg::v12s2 => 32,
            Arm64Reg::v12s3 => 32,
            Arm64Reg::v13s0 => 32,
            Arm64Reg::v13s1 => 32,
            Arm64Reg::v13s2 => 32,
            Arm64Reg::v13s3 => 32,
            Arm64Reg::v14s0 => 32,
            Arm64Reg::v14s1 => 32,
            Arm64Reg::v14s2 => 32,
            Arm64Reg::v14s3 => 32,
            Arm64Reg::v15s0 => 32,
            Arm64Reg::v15s1 => 32,
            Arm64Reg::v15s2 => 32,
            Arm64Reg::v15s3 => 32,
            Arm64Reg::v16s0 => 32,
            Arm64Reg::v16s1 => 32,
            Arm64Reg::v16s2 => 32,
            Arm64Reg::v16s3 => 32,
            Arm64Reg::v17s0 => 32,
            Arm64Reg::v17s1 => 32,
            Arm64Reg::v17s2 => 32,
            Arm64Reg::v17s3 => 32,
            Arm64Reg::v18s0 => 32,
            Arm64Reg::v18s1 => 32,
            Arm64Reg::v18s2 => 32,
            Arm64Reg::v18s3 => 32,
            Arm64Reg::v19s0 => 32,
            Arm64Reg::v19s1 => 32,
            Arm64Reg::v19s2 => 32,
            Arm64Reg::v19s3 => 32,
            Arm64Reg::v20s0 => 32,
            Arm64Reg::v20s1 => 32,
            Arm64Reg::v20s2 => 32,
            Arm64Reg::v20s3 => 32,
            Arm64Reg::v21s0 => 32,
            Arm64Reg::v21s1 => 32,
            Arm64Reg::v21s2 => 32,
            Arm64Reg::v21s3 => 32,
            Arm64Reg::v22s0 => 32,
            Arm64Reg::v22s1 => 32,
            Arm64Reg::v22s2 => 32,
            Arm64Reg::v22s3 => 32,
            Arm64Reg::v23s0 => 32,
            Arm64Reg::v23s1 => 32,
            Arm64Reg::v23s2 => 32,
            Arm64Reg::v23s3 => 32,
            Arm64Reg::v24s0 => 32,
            Arm64Reg::v24s1 => 32,
            Arm64Reg::v24s2 => 32,
            Arm64Reg::v24s3 => 32,
            Arm64Reg::v25s0 => 32,
            Arm64Reg::v25s1 => 32,
            Arm64Reg::v25s2 => 32,
            Arm64Reg::v25s3 => 32,
            Arm64Reg::v26s0 => 32,
            Arm64Reg::v26s1 => 32,
            Arm64Reg::v26s2 => 32,
            Arm64Reg::v26s3 => 32,
            Arm64Reg::v27s0 => 32,
            Arm64Reg::v27s1 => 32,
            Arm64Reg::v27s2 => 32,
            Arm64Reg::v27s3 => 32,
            Arm64Reg::v28s0 => 32,
            Arm64Reg::v28s1 => 32,
            Arm64Reg::v28s2 => 32,
            Arm64Reg::v28s3 => 32,
            Arm64Reg::v29s0 => 32,
            Arm64Reg::v29s1 => 32,
            Arm64Reg::v29s2 => 32,
            Arm64Reg::v29s3 => 32,
            Arm64Reg::v30s0 => 32,
            Arm64Reg::v30s1 => 32,
            Arm64Reg::v30s2 => 32,
            Arm64Reg::v30s3 => 32,
            Arm64Reg::v31s0 => 32,
            Arm64Reg::v31s1 => 32,
            Arm64Reg::v31s2 => 32,
            Arm64Reg::v31s3 => 32,
            Arm64Reg::v0d0 => 64,
            Arm64Reg::v0d1 => 64,
            Arm64Reg::v1d0 => 64,
            Arm64Reg::v1d1 => 64,
            Arm64Reg::v2d0 => 64,
            Arm64Reg::v2d1 => 64,
            Arm64Reg::v3d0 => 64,
            Arm64Reg::v3d1 => 64,
            Arm64Reg::v4d0 => 64,
            Arm64Reg::v4d1 => 64,
            Arm64Reg::v5d0 => 64,
            Arm64Reg::v5d1 => 64,
            Arm64Reg::v6d0 => 64,
            Arm64Reg::v6d1 => 64,
            Arm64Reg::v7d0 => 64,
            Arm64Reg::v7d1 => 64,
            Arm64Reg::v8d0 => 64,
            Arm64Reg::v8d1 => 64,
            Arm64Reg::v9d0 => 64,
            Arm64Reg::v9d1 => 64,
            Arm64Reg::v10d0 => 64,
            Arm64Reg::v10d1 => 64,
            Arm64Reg::v11d0 => 64,
            Arm64Reg::v11d1 => 64,
            Arm64Reg::v12d0 => 64,
            Arm64Reg::v12d1 => 64,
            Arm64Reg::v13d0 => 64,
            Arm64Reg::v13d1 => 64,
            Arm64Reg::v14d0 => 64,
            Arm64Reg::v14d1 => 64,
            Arm64Reg::v15d0 => 64,
            Arm64Reg::v15d1 => 64,
            Arm64Reg::v16d0 => 64,
            Arm64Reg::v16d1 => 64,
            Arm64Reg::v17d0 => 64,
            Arm64Reg::v17d1 => 64,
            Arm64Reg::v18d0 => 64,
            Arm64Reg::v18d1 => 64,
            Arm64Reg::v19d0 => 64,
            Arm64Reg::v19d1 => 64,
            Arm64Reg::v20d0 => 64,
            Arm64Reg::v20d1 => 64,
            Arm64Reg::v21d0 => 64,
            Arm64Reg::v21d1 => 64,
            Arm64Reg::v22d0 => 64,
            Arm64Reg::v22d1 => 64,
            Arm64Reg::v23d0 => 64,
            Arm64Reg::v23d1 => 64,
            Arm64Reg::v24d0 => 64,
            Arm64Reg::v24d1 => 64,
            Arm64Reg::v25d0 => 64,
            Arm64Reg::v25d1 => 64,
            Arm64Reg::v26d0 => 64,
            Arm64Reg::v26d1 => 64,
            Arm64Reg::v27d0 => 64,
            Arm64Reg::v27d1 => 64,
            Arm64Reg::v28d0 => 64,
            Arm64Reg::v28d1 => 64,
            Arm64Reg::v29d0 => 64,
            Arm64Reg::v29d1 => 64,
            Arm64Reg::v30d0 => 64,
            Arm64Reg::v30d1 => 64,
            Arm64Reg::v31d0 => 64,
            Arm64Reg::v31d1 => 64,
        }
    }
}

impl Register for Arm64Reg {
    fn id(&self) -> u32 {
        *self as u32
    }
}

impl std::fmt::Display for Arm64Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
