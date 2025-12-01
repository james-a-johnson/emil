use crate::arch::{Endian, Little};
use crate::arch::{FileDescriptor, Intrinsic, RegState, State, SyscallResult};
use crate::os::linux::LinuxSyscalls;
use binaryninja::architecture::{Intrinsic as _, Register as BNReg};
use binaryninja::low_level_il::expression::ExpressionHandler;
use binaryninja::low_level_il::expression::LowLevelILExpressionKind as ExprKind;
use binaryninja::low_level_il::operation::IntrinsicOutput;
use regs::Register as _;
use softmew::page::SimplePage;
use softmew::{MMU, Perm};
use val::ILVal;

use std::collections::{HashMap, VecDeque};
use std::ffi::{CString, OsString};
use std::fs::OpenOptions;
use std::ops::Range;
use std::os::unix::ffi::OsStringExt;
use std::path::PathBuf;

pub use regs::aarch64::{aarch64Reg as Arm64Reg, aarch64RegFile as Arm64State};

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
            "SystemHintOp_BTI" => Ok(Self::BtiHint),
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
            "__ldaxr" | "__ldxr" => {
                // ldaxr, load acquire exclusive
                let dest_reg = get_reg_from_outputs(intrinsic, 0)
                    .map_err(|e| format!("Couldn't get register to load into for ldaxr: {e}"))?;
                let source_reg = get_reg_from_inputs(intrinsic, 0)
                    .map_err(|e| format!("Couldn't get source register for ldaxr: {e}"))?;
                Ok(Self::Ldxr(dest_reg, source_reg))
            }
            "__stlxr" | "__stxr" => {
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
        self.regs.lr = addr;
        Ok(())
    }

    fn push(&mut self, val: &[u8]) -> Result<(), softmew::fault::Fault> {
        let mut sp = self.regs.sp;
        sp -= val.len() as u64;
        self.regs.sp = sp;
        self.mem.write_perm(sp as usize, val)
    }

    fn pop(&mut self, data: &mut [u8]) -> Result<(), softmew::fault::Fault> {
        let sp = self.regs.sp;
        self.regs.sp = sp - data.len() as u64;
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
                self.mem
                    .read_perm(addr, &mut buf[0..dest.size() as usize])?;
                let val = Little::read(&buf[0..dest.size() as usize]);
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
                        self.regs.write(*reg, &ILVal::Quad(self.tpid));
                        Ok(())
                    }
                    x => panic!("Implement reading msr {x:#x}"),
                }
            }
            ArmIntrinsic::WriteMSR(reg, msr) => {
                match msr {
                    0xde82 => {
                        // TPIDR_EL0, Thread ID Register
                        self.tpid = self.regs.read(*reg).get_quad();
                        Ok(())
                    }
                    x => panic!("Implement writing msr {x:#x}"),
                }
            }
        }
    }

    fn syscall(&mut self, _addr: u64) -> super::SyscallResult {
        let syscall_no = self.regs.x8 as u32;
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
        self.regs.x0 = val.extend_64()
    }

    fn read(&mut self) -> SyscallResult {
        let fd = self.regs.x0;
        let ptr = self.regs.x1 as usize;
        let len = self.regs.x2 as usize;
        let data = self
            .mem
            .get_slice_mut(ptr..ptr + len, Perm::WRITE)
            .expect("Reading to invalid memory");
        match self.fds.get_mut(&(fd as u32)) {
            Some(file) => {
                let res = file.read(data);
                match res {
                    Ok(b) => {
                        self.regs.x0 = b as u64;
                    }
                    Err(e) => {
                        self.regs.x0 = e.raw_os_error().unwrap_or(-9) as u64;
                    }
                }
            }
            None => self.regs.x0 = (-9_i64) as u64,
        };
        SyscallResult::Continue
    }

    fn write(&mut self) -> SyscallResult {
        let fd = self.regs.x0;
        let ptr = self.regs.x1 as usize;
        let len = self.regs.x2 as usize;
        let data = self
            .mem
            .get_slice(ptr..ptr + len, Perm::READ)
            .expect("Failed to read data");
        match self.fds.get_mut(&(fd as u32)) {
            Some(file) => {
                let res = file.write(&data);
                match res {
                    Ok(b) => self.regs.x0 = b as u64,
                    Err(e) => {
                        self.regs.x0 = e.raw_os_error().unwrap_or(-9) as u64;
                    }
                }
            }
            None => self.regs.x0 = len as u64,
        }
        SyscallResult::Continue
    }

    fn set_tid_address(&mut self) -> SyscallResult {
        self.regs.x0 = 100;
        SyscallResult::Continue
    }

    fn set_robust_list(&mut self) -> SyscallResult {
        self.regs.x0 = 0;
        SyscallResult::Continue
    }

    fn futex(&mut self) -> SyscallResult {
        self.regs.x0 = 0;
        SyscallResult::Continue
    }

    fn getrandom(&mut self) -> SyscallResult {
        let buf = self.regs.x0 as usize;
        let len = self.regs.x1 as usize;
        let buffer = match self.mem.get_slice_mut(buf..buf + len, Perm::WRITE) {
            Ok(s) => s,
            Err(_) => {
                self.regs.x0 = (-14_i64) as u64;
                return SyscallResult::Continue;
            }
        };
        buffer.fill(0xaa);
        self.regs.x0 = len as u64;
        SyscallResult::Continue
    }

    fn uname(&mut self) -> SyscallResult {
        let addr = self.regs.x0;
        self.regs.x0 = (-14_i64) as u64;
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
        self.regs.x0 = 0;
        SyscallResult::Continue
    }

    fn getuid(&mut self) -> SyscallResult {
        self.regs.x0 = 1000;
        SyscallResult::Continue
    }

    fn geteuid(&mut self) -> SyscallResult {
        self.regs.x0 = 1000;
        SyscallResult::Continue
    }

    fn getgid(&mut self) -> SyscallResult {
        self.regs.x0 = 1000;
        SyscallResult::Continue
    }

    fn getegid(&mut self) -> SyscallResult {
        self.regs.x0 = 1000;
        SyscallResult::Continue
    }

    fn brk(&mut self) -> SyscallResult {
        let addr = self.regs.x0;
        if addr < self.heap.start {
            self.regs.x0 = self.heap.start;
        } else if addr > self.heap.end {
            self.regs.x0 = self.heap.end;
        }
        SyscallResult::Continue
    }

    fn mmap(&mut self) -> SyscallResult {
        let addr = self.regs.x0;
        let len = self.regs.x1;

        if addr == 0 {
            // Just map at any address that has the required size
            let range = self.mem.gaps().find(|r| r.size() >= len as usize);
            if let Some(addrs) = range {
                let page = self
                    .mem
                    .map_memory(addrs.start, len as usize, Perm::READ | Perm::WRITE);
                if page.is_ok() {
                    self.regs.x0 = addrs.start as u64;
                    return SyscallResult::Continue;
                }
            }
            self.regs.x0 = u64::MAX;
            return SyscallResult::Continue;
        } else {
            let page = self
                .mem
                .map_memory(addr as usize, len as usize, Perm::READ | Perm::WRITE);
            if page.is_ok() {
                self.regs.x0 = addr;
                return SyscallResult::Continue;
            }
            self.regs.x0 = u64::MAX;
            return SyscallResult::Continue;
        }
    }

    fn mprotect(&mut self) -> SyscallResult {
        self.regs.x0 = 0;
        SyscallResult::Continue
    }

    fn writev(&mut self) -> SyscallResult {
        let _fd = self.regs.x0;
        let _iov = self.regs.x1;
        let _iocnt = self.regs.x2;
        SyscallResult::Continue
    }

    fn readlinkat(&mut self) -> SyscallResult {
        let mut path_addr = self.regs.x1;
        let mut path = Vec::new();
        let mut buf = [0u8];
        let bufsize = self.regs.x2 as usize;
        let copy_size = bufsize.min(self.progname.count_bytes());
        let link_buf = self.regs.x2;
        loop {
            if self.mem.read_perm(path_addr as usize, &mut buf).is_err() {
                self.regs.x0 = (-14_i64) as u64;
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
                    Ok(_) => self.regs.x0 = copy_size as u64,
                    Err(_) => self.regs.x0 = (-14_i16) as u64,
                };
            }
            _ => self.regs.x0 = (-2_i64) as u64,
        }
        SyscallResult::Continue
    }

    fn openat(&mut self) -> SyscallResult {
        let mut path_addr = self.regs.x1;
        let options = self.regs.x2 & 0xffffffff;
        let mut path = Vec::new();
        let mut buf = [0u8];
        loop {
            if self.mem.read_perm(path_addr as usize, &mut buf).is_err() {
                self.regs.x0 = (-14_i64) as u64;
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
                    self.regs.x0 = num as u64;
                }
                Err(e) => {
                    let errno = e.raw_os_error().unwrap_or(-2);
                    self.regs.x0 = errno as i64 as u64;
                }
            },
            Err(e) => {
                let errno = e.raw_os_error().unwrap_or(-2);
                self.regs.x0 = errno as i64 as u64;
            }
        };

        SyscallResult::Continue
    }

    fn close(&mut self) -> SyscallResult {
        let fd = self.regs.x0 as u32;
        if self.fds.contains_key(&fd) {
            // Don't actually close here because user of the emulator might want to get the file and look at it
            // themselves.
            self.regs.x0 = 0;
        } else {
            self.regs.x0 = (-77_i64) as u64;
        }
        SyscallResult::Continue
    }

    fn newfstatat(&mut self) -> SyscallResult {
        self.regs.x0 = (-2_i64) as u64;
        SyscallResult::Continue
    }
}
