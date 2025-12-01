// NOTE: To print out regs from Binja, you can use the following script in the python console
// ```python
// for (name, reg) in bv.arch.regs.items():
//     print(f"{name} = {reg.index}")
// ```

pub use regs::{RegState, Register};
pub use softmew::Perm;
pub use softmew::fault::Fault;
use softmew::page::Page;

use binaryninja::low_level_il::function::{Finalized, NonSSA};
use binaryninja::low_level_il::operation::{Intrinsic as LLILIntrinsic, Operation};
use softmew::MMU;

use std::error::Error;
use std::{
    any::Any,
    io::{Read, Write},
};

pub mod amd64;
pub mod arm64;
pub mod riscv;

use std::fmt::Debug;

use val::{Big as BigInt, ILVal};

/// Result of a system call.
///
/// This enum will indicate to the emulator how to continue execution after the state has emulated the given
/// system call.
pub enum SyscallResult {
    /// Continue executing at the next instruction.
    Continue,
    /// Stop execution. This would be returned from `exit_group` on Linux.
    Exit,
    /// Indicate that some memory fault occurred.
    ///
    /// This is unlikely to happen as most operating systems will return an error code instead of causing
    /// execution to stop. You can choose to return this to simplify the error handling of system calls.
    Error(Fault),
    /// Indicate that some implementation error has occurred.
    ///
    /// This could be some unexpected state was encountered or something is not implemented yet.
    Panic(Box<dyn Error>),
}

impl From<Fault> for SyscallResult {
    fn from(value: Fault) -> Self {
        Self::Error(value)
    }
}

/// Intrinsic instruction.
///
/// This is so that an intrinsic instruction can be parsed into some state that the state understands and can implement
/// and emulate behind the scenes.
///
/// If you want to be able to save state to disk, this this type will need to be serializable.
pub trait Intrinsic: Sized + Clone + Copy + Debug {
    /// Parse an intrinsic operation into the implementing type.
    fn parse(intrinsic: &Operation<'_, Finalized, NonSSA, LLILIntrinsic>) -> Result<Self, String>;
}

pub trait State<P: Page> {
    type Registers: RegState;
    type Endianness: Endian;
    type Intrin: Intrinsic;

    /// Get registers from state.
    fn regs(&mut self) -> &mut Self::Registers;
    /// Get memory associated with the state.
    fn mem(&mut self) -> &mut MMU<P>;

    /// Get references to the registers and memory.
    fn underlying(&mut self) -> (&mut Self::Registers, &mut MMU<P>);

    /// Read flag value with the given id.
    fn get_flag(&self, id: u32) -> bool;
    /// Write flag value with the given id.
    fn set_flag(&mut self, val: bool, id: u32);

    /// Emulate a syscall.
    ///
    /// `addr` is the address of the system call instruction to be emulated.
    ///
    /// It is up to the implementor to get the system call number from the state and then determine how to correctly
    /// emulate that system call.
    fn syscall(&mut self, addr: u64) -> SyscallResult;
    /// Emulate an intrinsic instruction.
    fn intrinsic(&mut self, intrin: &Self::Intrin) -> Result<(), Fault>;

    /// Save the given return address.
    ///
    /// Different architectures will save return addresses in different ways. An x86 state should push the value onto
    /// the stack whereas an arm state should write the value to the link register.
    fn save_ret_addr(&mut self, addr: u64) -> Result<(), Fault>;
    /// Push data onto the stack.
    ///
    /// This should also update the stack pointer register.
    fn push(&mut self, val: &[u8]) -> Result<(), Fault>;
    /// Pop data off of the stack and read it into the buffer.
    ///
    /// This should also update the stack pointer register.
    fn pop(&mut self, data: &mut [u8]) -> Result<(), Fault>;
}

/// Helper trait that can be used as a trait for adding a file descriptor to some target's state.
///
/// Requires [`Read`] and [`Write`] so that the state can forwards reads and writes to the value.
/// Also requires [`Any`] so that it can be turned into a boxed trait object to pass ownership to
/// the state. Then you can get it back and downcast it to the original type.
pub trait FileDescriptor: Read + Write + Any {}

/// Implement trait for any type that implements all of the required traits.
impl<T: Read + Write + Any> FileDescriptor for T {}

pub trait Endian: Debug + Clone + Copy {
    fn read(data: &[u8]) -> ILVal;
    fn write(value: &ILVal, data: &mut [u8]);
}

#[derive(Debug, Clone, Copy)]
pub struct Little;
impl Endian for Little {
    fn read(data: &[u8]) -> ILVal {
        match data.len() {
            0 => unreachable!("Can't read a flag from memory"),
            1 => ILVal::Byte(data[0]),
            2 => ILVal::Short(u16::from_le_bytes(
                data.try_into().expect("Length is valid"),
            )),
            4 => ILVal::Word(u32::from_le_bytes(
                data.try_into().expect("Length is valid"),
            )),
            8 => ILVal::Quad(u64::from_le_bytes(
                data.try_into().expect("Length is valid"),
            )),
            _ => ILVal::Big(BigInt::from(data)),
        }
    }

    fn write(value: &ILVal, data: &mut [u8]) {
        match value {
            ILVal::Flag(_) => unreachable!("Can't write a flag"),
            ILVal::Byte(b) => {
                data[0] = *b;
            }
            ILVal::Short(s) => {
                data[0..2].copy_from_slice(&s.to_le_bytes());
            }
            ILVal::Word(w) => {
                data[0..4].copy_from_slice(&w.to_le_bytes());
            }
            ILVal::Quad(q) => {
                data[0..8].copy_from_slice(&q.to_le_bytes());
            }
            ILVal::Big(s) => {
                data.copy_from_slice(s.bytes());
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Big;

impl Endian for Big {
    fn read(data: &[u8]) -> ILVal {
        match data.len() {
            0 => unreachable!("Can't read flag from memory"),
            1 => ILVal::Byte(data[0]),
            2 => ILVal::Short(u16::from_be_bytes(
                data.try_into().expect("bength is valid"),
            )),
            4 => ILVal::Word(u32::from_be_bytes(
                data.try_into().expect("bength is valid"),
            )),
            8 => ILVal::Quad(u64::from_be_bytes(
                data.try_into().expect("bength is valid"),
            )),
            _ => ILVal::Big(BigInt::from_iter(data.iter().rev())),
        }
    }

    fn write(value: &ILVal, data: &mut [u8]) {
        match value {
            ILVal::Flag(_) => unreachable!("Can't write a flag"),
            ILVal::Byte(b) => {
                data[0] = *b;
            }
            ILVal::Short(s) => {
                data[0..2].copy_from_slice(&s.to_be_bytes());
            }
            ILVal::Word(w) => {
                data[0..4].copy_from_slice(&w.to_be_bytes());
            }
            ILVal::Quad(q) => {
                data[0..8].copy_from_slice(&q.to_be_bytes());
            }
            ILVal::Big(b) => {
                for (i, b) in b.bytes().iter().rev().enumerate() {
                    data[i] = *b;
                }
            }
        }
    }
}
