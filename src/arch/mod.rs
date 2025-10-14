// NOTE: To print out regs from Binja, you can use the following script in the python console
// ```python
// for (name, reg) in bv.arch.regs.items():
//     print(f"{name} = {reg.index}")
// ```

pub use softmew::fault::Fault;

use binaryninja::low_level_il::function::{Finalized, NonSSA};
use binaryninja::low_level_il::operation::{Intrinsic as LLILIntrinsic, Operation};

use std::{
    any::Any,
    io::{Read, Write},
    ops::Range,
};

#[cfg(feature = "serde")]
use serde::{Serialize, de::Deserialize};

pub mod arm64;
pub mod riscv;

use std::fmt::{Debug, Display};

use crate::emil::ILVal;
use crate::emulate::Endian;

pub enum SyscallResult {
    Continue,
    Exit,
    Error(Fault),
}

pub trait Register: TryFrom<u32> + Debug + Display + Clone + Copy {
    fn syscall_ret() -> Self;
    fn id(&self) -> u32;
}

pub trait RegState {
    fn set_syscall_return(&mut self, val: ILVal);
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

pub trait State {
    type Reg: Register;
    type Endianness: Endian;
    type Intrin: Intrinsic;

    /// Read a register
    fn read_reg(&self, id: Self::Reg) -> ILVal;
    /// Set a register value
    fn write_reg(&mut self, id: Self::Reg, value: ILVal);

    /// Read from system memory
    fn read_mem(&self, addr: u64, buf: &mut [u8]) -> Result<(), Fault>;
    /// Write to system memory
    fn write_mem(&mut self, addr: u64, data: &[u8]) -> Result<(), Fault>;

    /// Get a range of addresses as a slice.
    fn get_mem(&self, addrs: Range<u64>) -> Result<&[u8], Fault>;
    /// Get a range of addresses as a mutable slice.
    fn get_mem_mut(&mut self, addrs: Range<u64>) -> Result<&mut [u8], Fault>;

    fn get_flag(&self, id: u32) -> bool;
    fn set_flag(&mut self, val: bool, id: u32);

    fn syscall(&mut self, addr: u64) -> SyscallResult;
    fn intrinsic(&mut self, intrin: &Self::Intrin) -> Result<(), Fault>;

    fn save_ret_addr(&mut self, addr: u64) -> Result<(), Fault>;
    fn push(&mut self, val: &[u8]) -> Result<(), Fault>;
    fn pop(&mut self, data: &mut [u8]) -> Result<(), Fault>;
}

#[cfg(feature = "serde")]
pub trait Saveable<'de>: State + Serialize + Deserialize<'de> {}

/// Helper trait that can be used as a trait for adding a file descriptor to some target's state.
///
/// Requires [`Read`] and [`Write`] so that the state can forwards reads and writes to the value.
/// Also requires [`Any`] so that it can be turned into a boxed trait object to pass ownership to
/// the state. Then you can get it back and downcast it to the original type.
pub trait FileDescriptor: Read + Write + Any {}

/// Implement trait for any type that implements all of the required traits.
impl<T: Read + Write + Any> FileDescriptor for T {}
