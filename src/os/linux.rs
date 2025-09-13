use crate::{arch::{RegState, Register, State, SyscallResult}, emil::ILVal};

/// Auxiliary vector entries.
#[derive(Clone, Copy, Debug)]
pub enum AuxVal {
    /// end of vector     
    Null,
    /// entry should be ignored     
    Ignore,
    /// file descriptor of program     
    Execfd,
    /// program headers for program     
    Phdr,
    /// size of program header entry     
    Phent,
    /// number of program headers     
    Phnum,
    /// system page size     
    Pagesz,
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
    Platform,
    /// arch dependent hints at CPU capabilities     
    Hwcap,
    /// frequency at which times() increments     
    Clktck,
    // AT_* values 18 through 22 are reserved
    /// secure mode boolean     
    Secure,
    /// string identifying real platform, may differ from AT_PLATFORM
    BasePlatform,
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
            Self::Phdr => 3,
            Self::Phent => 4,
            Self::Phnum => 5,
            Self::Pagesz => 6,
            Self::Base => 7,
            Self::Flags => 8,
            Self::Entry(_) => 9,
            Self::Notelf => 10,
            Self::Uid(_) => 11,
            Self::Euid(_) => 12,
            Self::Gid(_) => 13,
            Self::Egid(_) => 14,
            Self::Platform => 15,
            Self::Hwcap => 16,
            Self::Clktck => 17,
            Self::Secure => 23,
            Self::BasePlatform => 24,
            Self::Random(_) => 25,
            Self::Hwcap2 => 26,
            Self::RseqFeatureSize => 27,
            Self::RseqAlign => 28,
            Self::Hwcap3 => 29,
            Self::Hwcap4 => 30,
            Self::Execfn => 31,
            Self::Minsigstksz => 51,
        }
    }
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
        let mut current = top;
        let argc = self.args.len();
        let mut len = data.len();
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
                AuxVal::Uid(id) | AuxVal::Euid(id) | AuxVal::Gid(id) | AuxVal::Egid(id) => {
                    aux_vals.push((aux.discrim(), *id));
                }
                AuxVal::Random(rand) => {
                    len = len - 16;
                    current = current - 16;
                    data[len..][..16].copy_from_slice(rand);
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
        fn $name(&mut self, regs: &mut R, _mem: &mut M) -> SyscallResult {
            regs.set_syscall_return(UNIMPLEMENTED);
            SyscallResult::Continue
        }
    };
}

pub trait LinuxSyscalls<R: RegState, M> {
    define_syscall!(faccessat);
    define_syscall!(openat);
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

    fn exit(&mut self, _regs: &mut R, _mem: &mut M) -> SyscallResult {
        SyscallResult::Exit
    }
    
}
