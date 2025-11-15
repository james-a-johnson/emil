use std::ffi::OsString;

use binaryninja::binary_view::BinaryViewExt;

use crate::{arch::SyscallResult, emil::ILVal};

/// Auxiliary vector entries.
#[derive(Clone, Debug)]
pub enum AuxVal {
    /// end of vector
    Null,
    /// entry should be ignored
    Ignore,
    /// file descriptor of program
    Execfd,
    /// program headers for program
    Phdr(u64),
    /// size of program header entry
    Phent(u64),
    /// number of program headers
    Phnum(u64),
    /// system page size
    Pagesz(u64),
    /// base address of interpreter
    Base,
    /// flags
    Flags,
    /// entry point of program
    Entry(u64),
    /// program is not ELF
    Notelf,
    /// real uid
    Uid(u64),
    /// effective uid
    Euid(u64),
    /// real gid
    Gid(u64),
    /// effective gid
    Egid(u64),
    /// string identifying CPU for optimizations
    Platform(OsString),
    /// arch dependent hints at CPU capabilities
    Hwcap(u64),
    /// frequency at which times() increments
    Clktck,
    // AT_* values 18 through 22 are reserved
    /// secure mode boolean
    Secure,
    /// string identifying real platform, may differ from AT_PLATFORM
    BasePlatform(OsString),
    /// address of 16 random bytes
    Random([u8; 16]),
    /// extension of AT_HWCAP
    Hwcap2,
    /// rseq supported feature size
    RseqFeatureSize,
    /// rseq allocation alignment
    RseqAlign,
    /// extension of AT_HWCAP
    Hwcap3,
    /// extension of AT_HWCAP
    Hwcap4,
    /// filename of program
    Execfn,
    /// Location of vDSO if present
    SysinfoEhdr(u64),
    /// Minimum stack size for signal stack
    Minsigstksz,
}

impl AuxVal {
    pub fn size_required(&self) -> usize {
        match self {
            Self::Random(_) => 32,
            _ => 16,
        }
    }

    pub fn discrim(&self) -> u64 {
        match self {
            Self::Null => 0,
            Self::Ignore => 1,
            Self::Execfd => 2,
            Self::Phdr(_) => 3,
            Self::Phent(_) => 4,
            Self::Phnum(_) => 5,
            Self::Pagesz(_) => 6,
            Self::Base => 7,
            Self::Flags => 8,
            Self::Entry(_) => 9,
            Self::Notelf => 10,
            Self::Uid(_) => 11,
            Self::Euid(_) => 12,
            Self::Gid(_) => 13,
            Self::Egid(_) => 14,
            Self::Platform(_) => 15,
            Self::Hwcap(_) => 16,
            Self::Clktck => 17,
            Self::Secure => 23,
            Self::BasePlatform(_) => 24,
            Self::Random(_) => 25,
            Self::Hwcap2 => 26,
            Self::RseqFeatureSize => 27,
            Self::RseqAlign => 28,
            Self::Hwcap3 => 29,
            Self::Hwcap4 => 30,
            Self::Execfn => 31,
            Self::SysinfoEhdr(_) => 33,
            Self::Minsigstksz => 51,
        }
    }
}

pub fn add_default_auxv(auxv: &mut Vec<AuxVal>, binary: &binaryninja::binary_view::BinaryView) {
    auxv.push(AuxVal::Uid(1000));
    auxv.push(AuxVal::Gid(1000));
    auxv.push(AuxVal::Euid(1000));
    auxv.push(AuxVal::Egid(1000));
    auxv.push(AuxVal::Pagesz(0x1000));
    if let Some(arch) = binary.default_arch() {
        auxv.push(AuxVal::Platform(arch.name().into()));
    }
    if let Some(entry) = binary.entry_point_function() {
        auxv.push(AuxVal::Entry(entry.start()));
    }
    auxv.push(AuxVal::Random([
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    ]));
    auxv.push(AuxVal::SysinfoEhdr(0));
}

/// Environment that a linux process will start with.
///
/// This includes the arguments, environment, and auxiliary vector that will be
/// used.
///
/// The fields in this are public so just push strings or axiliary values to
/// the respective vector and everything will be handled for you. A valid
/// String will have a valid representation in the memory space so you don't
/// need to worry about fixing it in any way. This does limit what can be used
/// here as there are valid parameters that are not valid strings.
///
/// It seems like glibc relies on a [`AuxVal::Random`] existing on the stack
/// somewhere or else the program will segmentation fault. I recommend adding
/// one of those to the program to make sure it works. [`Environment::encode`]
/// will handle adding a [`AuxVal::Nul`] to the end so you don't need to worry
/// about doing that yourself.
#[derive(Default)]
pub struct Environment {
    pub args: Vec<String>,
    pub env: Vec<String>,
    pub aux: Vec<AuxVal>,
}

impl Environment {
    pub fn encode(&self, data: &mut [u8], top: u64) -> Result<u64, ()> {
        data.fill(0);
        let mut current = top - 0x10;
        let argc = self.args.len();
        let mut len = data.len() - 0x10;
        let mut env_ptrs = Vec::new();
        let mut arg_ptrs = Vec::new();
        let mut aux_vals: Vec<(u64, u64)> = Vec::new();
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
        while len % 8 != 0 {
            len -= 1;
            current -= 1;
        }
        // Make sure aux vector ends in null
        aux_vals.push((AuxVal::Null.discrim(), 0));
        for aux in self.aux.iter() {
            match aux {
                AuxVal::Uid(id)
                | AuxVal::Euid(id)
                | AuxVal::Gid(id)
                | AuxVal::Egid(id)
                | AuxVal::Hwcap(id)
                | AuxVal::Phnum(id)
                | AuxVal::Phdr(id)
                | AuxVal::Phent(id)
                | AuxVal::SysinfoEhdr(id)
                | AuxVal::Entry(id)
                | AuxVal::Pagesz(id) => {
                    aux_vals.push((aux.discrim(), *id));
                }
                AuxVal::Random(rand) => {
                    len = len - 16;
                    current = current - 16;
                    data[len..][..16].copy_from_slice(rand);
                    aux_vals.push((aux.discrim(), current));
                }
                AuxVal::Platform(s) | AuxVal::BasePlatform(s) => {
                    len = len - s.len() - 1;
                    current = current - (s.len() as u64) - 1;
                    data[len..][..s.len()].copy_from_slice(s.as_encoded_bytes());
                    aux_vals.push((aux.discrim(), current));
                }
                _ => unimplemented!("Haven't done {:?} yet", aux),
            }
        }
        while len % 64 != 0 {
            len -= 1;
            current -= 1;
        }
        for auxv in aux_vals {
            let (id, val) = auxv;
            len -= 8;
            current -= 8;
            data[len..][..8].copy_from_slice(&val.to_le_bytes());
            len -= 8;
            current -= 8;
            data[len..][..8].copy_from_slice(&id.to_le_bytes());
        }
        len -= 8;
        current -= 8;
        for ptr in env_ptrs {
            len -= 8;
            current -= 8;
            data[len..][..8].copy_from_slice(&ptr.to_le_bytes());
        }
        len -= 8;
        current -= 8;
        // Need to do these in reverse order
        arg_ptrs.reverse();
        for ptr in arg_ptrs {
            len -= 8;
            current -= 8;
            data[len..][..8].copy_from_slice(&ptr.to_le_bytes());
        }
        len -= 8;
        current -= 8;
        data[len..][..8].copy_from_slice(&argc.to_le_bytes());
        Ok(current)
    }
}

/// Errno for ENOTSUP.
pub const UNIMPLEMENTED: ILVal = ILVal::Quad((-95_i64) as u64);

macro_rules! define_syscall {
    ($name:ident) => {
        fn $name(&mut self) -> SyscallResult {
            self.set_syscall_return(UNIMPLEMENTED);
            SyscallResult::Continue
        }
    };
}

/// All of the Linux system calls.
///
/// **NOTE:** Not all of the system calls are currently implemented here. Adding
/// all of them is still a work in progress.
///
/// This trait provides a default implementation for each system call that just
/// returns an error saying the operation is not supported. Some syscalls have
/// different default returns. Those will have their default implementation
/// defined in a doc comment.
pub trait LinuxSyscalls {
    /// Set the return value of the system call.
    fn set_syscall_return(&mut self, ret: ILVal);

    define_syscall!(faccessat);
    define_syscall!(read);
    define_syscall!(write);
    define_syscall!(set_tid_address);
    define_syscall!(set_robust_list);
    define_syscall!(uname);
    define_syscall!(getuid);
    define_syscall!(geteuid);
    define_syscall!(getgid);
    define_syscall!(getegid);
    define_syscall!(brk);
    define_syscall!(prlimit64);
    define_syscall!(readlinkat);
    define_syscall!(getrandom);
    define_syscall!(clock_gettime);
    define_syscall!(mmap);
    define_syscall!(munmap);
    define_syscall!(writev);
    define_syscall!(rseq);
    define_syscall!(mprotect);
    define_syscall!(newfstatat);
    define_syscall!(futex);

    /// Returns that the path could not be found on the system.
    fn openat(&mut self) -> SyscallResult {
        self.set_syscall_return(ILVal::Quad((-2_i64) as u64));
        SyscallResult::Continue
    }

    /// Causes the emulator to stop execution.
    fn exit(&mut self) -> SyscallResult {
        SyscallResult::Exit
    }

    /// Causes the emulator to stop execution.
    fn exit_group(&mut self) -> SyscallResult {
        SyscallResult::Exit
    }

    /// Close a file descriptor.
    ///
    /// Default implementation always returns success.
    fn close(&mut self) -> SyscallResult {
        self.set_syscall_return(ILVal::Quad(0));
        SyscallResult::Continue
    }
}
