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
pub mod generic;
pub mod riscv;

use std::fmt::{Debug, Display};

use crate::emil::ILVal;

pub enum SyscallResult {
    Continue,
    Exit,
    Error(Fault),
}

pub trait Register: TryFrom<u32> + Debug + Display + Clone + Copy {
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

pub trait Endian: Debug + Clone + Copy {
    fn read(data: &[u8]) -> ILVal;
    fn write(value: ILVal, data: &mut [u8]) -> usize;
}

#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Little;
impl Endian for Little {
    fn read(data: &[u8]) -> ILVal {
        match data.len() {
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
            16 => ILVal::Simd(u128::from_le_bytes(
                data.try_into().expect("Length is valid"),
            )),
            _ => unreachable!("Invalid length"),
        }
    }

    fn write(value: ILVal, data: &mut [u8]) -> usize {
        match value {
            ILVal::Flag(_) => unreachable!("Can't write a flag"),
            ILVal::Byte(b) => {
                data[0] = b;
                1
            }
            ILVal::Short(s) => {
                data[0..2].copy_from_slice(&s.to_le_bytes());
                2
            }
            ILVal::Word(w) => {
                data[0..4].copy_from_slice(&w.to_le_bytes());
                4
            }
            ILVal::Quad(q) => {
                data[0..8].copy_from_slice(&q.to_le_bytes());
                8
            }
            ILVal::Simd(s) => {
                data.copy_from_slice(&s.to_le_bytes());
                16
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Big;

impl Endian for Big {
    fn read(data: &[u8]) -> ILVal {
        match data.len() {
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
            16 => ILVal::Simd(u128::from_be_bytes(
                data.try_into().expect("Length is valid"),
            )),
            _ => unreachable!("Invalid length"),
        }
    }

    fn write(value: ILVal, data: &mut [u8]) -> usize {
        match value {
            ILVal::Flag(_) => unreachable!("Can't write a flag"),
            ILVal::Byte(b) => {
                data[0] = b;
                1
            }
            ILVal::Short(s) => {
                data[0..2].copy_from_slice(&s.to_be_bytes());
                2
            }
            ILVal::Word(w) => {
                data[0..4].copy_from_slice(&w.to_be_bytes());
                4
            }
            ILVal::Quad(q) => {
                data[0..8].copy_from_slice(&q.to_be_bytes());
                8
            }
            ILVal::Simd(s) => {
                data.copy_from_slice(&s.to_be_bytes());
                16
            }
        }
    }
}
