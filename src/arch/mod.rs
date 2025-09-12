// NOTE: To print out regs from Binja, you can use the following script in the python console
// ```python
// for (name, reg) in bv.arch.regs.items():
//     print(f"{name} = {reg.index}")
// ```

pub use softmew::fault::Fault;

use std::{
    any::Any,
    io::{Read, Write},
};

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
    /// Get the register used as the stack register
    fn stack() -> Self;
}

pub trait State {
    type Reg: Register;
    type Endianness: Endian;

    /// Read a register
    fn read_reg(&self, id: Self::Reg) -> ILVal;
    /// Set a register value
    fn write_reg(&mut self, id: Self::Reg, value: ILVal);

    /// Read from system memory
    fn read_mem(&self, addr: u64, buf: &mut [u8]) -> Result<(), Fault>;
    /// Write to system memory
    fn write_mem(&mut self, addr: u64, data: &[u8]) -> Result<(), Fault>;

    fn get_flags(&self) -> u64;
    fn set_flags(&mut self, val: ILVal);

    fn syscall(&mut self) -> SyscallResult;

    fn save_ret_addr(&mut self, addr: u64) -> Result<(), Fault>;
    fn push(&mut self, val: &[u8]) -> Result<(), Fault>;
    fn pop(&mut self, data: &mut [u8]) -> Result<(), Fault>;
    fn intrinsic(&mut self, id: u32) -> Result<(), Fault>;
}

/// Helper trait that can be used as a trait for adding a file descriptor to some target's state.
///
/// Requires [`Read`] and [`Write`] so that the state can forwards reads and writes to the value.
/// Also requires [`Any`] so that it can be turned into a boxed trait object to pass ownership to
/// the state. Then you can get it back and downcast it to the original type.
pub trait FileDescriptor: Read + Write + Any {}

/// Implement trait for any type that implements all of the required traits.
impl<T: Read + Write + Any> FileDescriptor for T {}
