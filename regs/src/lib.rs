use std::fmt::{Debug, Display};
use val::ILVal;

pub mod aarch64;
pub mod rv64gc;
pub mod x86;
pub mod x86_64;

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
pub trait Register: TryFrom<u32> + Debug + Display + Clone + Copy {
    /// Size of the specific register in bytes.
    fn size(&self) -> u8;
}

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

#[cfg(test)]
mod test {
    use super::*;
    use crate::x86::{x86Reg as X86, x86RegFile as X86State};
    use val::Big;

    #[test]
    fn x86_basics() {
        let mut regs = X86State::default();
        assert_eq!(regs.eax, 0, "Default values are zero");
        let eax = regs.read(X86::eax);
        assert_eq!(eax, ILVal::Word(0), "Reading eax returns a word");
        regs.write(X86::eax, &ILVal::Word(100));
        assert_eq!(regs.eax, 100, "Writing eax should change its value");
        let eax = regs.read(X86::eax);
        assert_eq!(eax, ILVal::Word(100), "Reading eax returns updated value");

        let st6 = regs.read(X86::st6);
        assert_eq!(
            st6,
            ILVal::Big(Big::from([0, 0, 0, 0, 0, 0, 0, 0, 0, 0])),
            "Array register should return proper big value"
        );
        regs.write(
            X86::mm6,
            &ILVal::Quad(u64::from_le_bytes([1, 2, 3, 4, 5, 6, 7, 8])),
        );
        assert_eq!(
            regs.st6,
            [1, 2, 3, 4, 5, 6, 7, 8, 0, 0],
            "Setting array register sets proper bytes"
        );
    }
}
