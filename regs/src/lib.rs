use std::fmt::{Debug, Display};
use val::ILVal;

const _: () = assert!(
    0xaabb_u16.to_le_bytes()[0] == 0xbb,
    "This crate only supports little endian hosts"
);

/// Type that represents a specific register in an architecture.
///
/// In general, this should be represented by some enum that has each register as a variant. However, it
/// is up to the implementor to decide exactly how they want to represent the register.
///
/// Since Binary Ninja represents each regiter using a unique u32, the type needs to implement [`TryFrom`]
/// for a u32 so that it can be parsed out from an LLIL instruction when being convereted to the internal
/// representation.
pub trait Register: TryFrom<u32> + Debug + Display + Clone + Copy {}

/// State of all of the registers of a system.
pub trait RegState {
    type RegID: Register;

    /// Read the register with the given ID.
    fn read(&self, id: Self::RegID) -> ILVal;

    /// Set the register to the given value.
    ///
    /// You may assume that the `val` has the correct size for the register.
    /// Binary Ninja will correctly size the value for the given register
    /// write so if the value has the wrong size then the program is invalid
    /// and it makes sense to panic.
    fn write(&mut self, id: Self::RegID, val: &ILVal);
}
