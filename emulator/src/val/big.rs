//! Big integer type for an IL value.
//!
//! This is what is used to represent any non-standard or large sized value. The goal is to be fast enough for general
//! use but this is intended to be the slow path so that the other parts of [`ILVal`] can be fast.
//!
//! This is not a general purpose big integer type. It is made specifically to be used in this library and will not
//! work well outside of it. It assumes that it will be used the way that the emulator is using it. Otherwise, you
//! may find that it will panic on some of the operations that you would expect to succeed.
//!
//! Not all operations are currently implemented for this type. Currently missing are:
//! - Division
//! - Arithmetic shift
//! - Left shift
//! - Right shift

use crate::val::ILVal;

use std::fmt::{Debug, LowerHex, UpperHex};
use std::ops::{Add, BitAnd, BitOr, BitXor, Mul, Neg, Not, Sub};

/// Big integer type that can represent any number of bytes.
///
/// Internal representation is a little endian array of bytes.
#[repr(transparent)]
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct Big(Vec<u8>);

impl Big {
    /// Number of bytes in the big integer.
    #[inline]
    pub fn size(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub fn truth(&self) -> bool {
        self.0.iter().any(|b| *b != 0)
    }

    #[inline]
    pub fn bytes(&self) -> &[u8] {
        self.0.as_ref()
    }

    /// Create a big integer from an iterator of bytes.
    ///
    /// Assumes that the bytes are being iterated in little endian format.
    pub fn from_iter<'a, T: Iterator<Item = &'a u8>>(iter: T) -> Self {
        let mut bytes = Vec::with_capacity(iter.size_hint().0);
        for b in iter {
            bytes.push(*b);
        }
        Self(bytes)
    }

    /// Truncate the number to a specific number of bytes.
    ///
    /// This returns an [`ILVal`] instead of self so that it can return a u64 if it's truncating to 8 bytes or something
    /// similar.
    pub fn truncate(&self, size: u8) -> ILVal {
        debug_assert!(
            (size as usize) < self.size(),
            "Must truncate to smaller size"
        );
        match size {
            0 => ILVal::Flag(self.0[0] & 0b1 == 1),
            1 => ILVal::Byte(self.0[0]),
            2 => ILVal::Short(u16::from_le_bytes(self.0[0..2].try_into().unwrap())),
            4 => ILVal::Word(u32::from_le_bytes(self.0[0..4].try_into().unwrap())),
            8 => ILVal::Quad(u64::from_le_bytes(self.0[0..8].try_into().unwrap())),
            _ => ILVal::Big(Big(self.0[0..size as usize].to_vec())),
        }
    }

    /// Sign extend the big intenger to the specified number of bytes.
    pub fn sext(&self, size: u8) -> ILVal {
        debug_assert!(
            (size as usize) > self.size(),
            "Need to extend to a larger size"
        );
        // There are other ILValues for bytes of 0, 1, and 2. So this will never extend to one of those sizes
        // because anything that can extend to one of those sizes is something with a more specific ILValue
        // implementation.
        //
        // Just need to handle the special cases for sign extending to a specific ILVal and then the general
        // case for sign extending to a different sized big integer.
        match size {
            0..=2 => unreachable!("Extending from and to a specific ILVal size"),
            4 => {
                debug_assert_eq!(
                    self.size(),
                    3,
                    "This is the only case where this can happen"
                );
                let sign = if self.0[2] & 0b10000000 != 0 {
                    0xff
                } else {
                    0x00
                };
                let word = [self.0[0], self.0[1], self.0[2], sign];
                ILVal::Word(u32::from_le_bytes(word))
            }
            8 => {
                let mut quad = [0u8; 8];
                let last = self.size() - 1;
                let sign = if self.0[last] & 0b10000000 != 0 {
                    0xff
                } else {
                    0x00
                };
                let mut idx = 0;
                while idx < self.size() {
                    quad[idx] = self.0[idx];
                    idx += 1;
                }
                while idx < 8 {
                    quad[idx] = sign;
                    idx += 1;
                }
                ILVal::Quad(u64::from_le_bytes(quad))
            }
            _ => {
                let mut bytes = Vec::with_capacity(size.into());
                bytes.clone_from(&self.0);
                let last = self.size() - 1;
                let sign = if self.0[last] & 0b10000000 != 0 {
                    0xff
                } else {
                    0x00
                };
                let extension = (size as usize) - self.size();
                for _ in 0..extension {
                    bytes.push(sign);
                }
                ILVal::Big(Big(bytes))
            }
        }
    }

    /// Zero extend the big intenger to the specified number of bytes.
    pub fn zext(&self, size: u8) -> ILVal {
        debug_assert!(
            (size as usize) > self.size(),
            "Need to extend to a larger size"
        );
        // See the comment in sext for why specific values here are implemented the way they are.
        match size {
            0..=2 => unreachable!("Extending from and to a specific ILVal size"),
            4 => {
                debug_assert_eq!(
                    self.size(),
                    3,
                    "This is the only case where this can happen"
                );
                let word = [self.0[0], self.0[1], self.0[2], 0x00];
                ILVal::Word(u32::from_le_bytes(word))
            }
            8 => {
                let mut quad = [0u8; 8];
                let mut idx = 0;
                while idx < self.size() {
                    quad[idx] = self.0[idx];
                    idx += 1;
                }
                while idx < 8 {
                    quad[idx] = 0x00;
                    idx += 1;
                }
                ILVal::Quad(u64::from_le_bytes(quad))
            }
            _ => {
                let mut bytes = Vec::with_capacity(size.into());
                bytes.clone_from(&self.0);
                let extension = (size as usize) - self.size();
                for _ in 0..extension {
                    bytes.push(0x00);
                }
                ILVal::Big(Big(bytes))
            }
        }
    }

    /// Reverse the underlying byte array.
    pub fn byte_reverse(&self) -> Self {
        let mut bytes = self.0.clone();
        bytes.reverse();
        Self(bytes)
    }

    /// Reverse the underlying byte array and the bits in each byte.
    pub fn bit_reverse(&self) -> Self {
        let mut bytes = self.0.clone();
        bytes.reverse();
        for b in &mut bytes {
            *b = b.reverse_bits();
        }
        Self(bytes)
    }
}

impl AsRef<[u8]> for Big {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl From<&[u8]> for Big {
    fn from(value: &[u8]) -> Self {
        Self(value.to_vec())
    }
}

impl<const N: usize> From<[u8; N]> for Big {
    fn from(value: [u8; N]) -> Self {
        Self(value.to_vec())
    }
}

impl Debug for Big {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.0.iter()).finish()
    }
}

impl LowerHex for Big {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for b in self.0.iter().rev() {
            write!(f, "{:x}", *b)?;
        }
        Ok(())
    }
}

impl UpperHex for Big {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for b in self.0.iter().rev() {
            write!(f, "{:X}", *b)?;
        }
        Ok(())
    }
}

impl Add for &Big {
    type Output = Big;

    fn add(self, rhs: Self) -> Self::Output {
        debug_assert!(self.size() == rhs.size(), "Must be the same size");
        let mut bytes = Vec::with_capacity(self.size());
        let mut carry = false;
        for (a, b) in self.0.iter().zip(rhs.0.iter()) {
            let (val, c) = a.carrying_add(*b, carry);
            bytes.push(val);
            carry = c;
        }
        Big(bytes)
    }
}

impl Sub for &Big {
    type Output = Big;

    fn sub(self, rhs: Self) -> Self::Output {
        debug_assert!(self.size() == rhs.size(), "Must be the same size");
        let mut bytes = Vec::with_capacity(self.size());
        let mut borrow = false;
        for (a, b) in self.0.iter().zip(rhs.0.iter()) {
            let (val, c) = a.borrowing_sub(*b, borrow);
            bytes.push(val);
            borrow = c;
        }
        Big(bytes)
    }
}

impl Mul for &Big {
    type Output = Big;

    fn mul(self, rhs: Self) -> Self::Output {
        debug_assert!(self.size() == rhs.size(), "Must be the same size");
        let mut bytes = vec![0u8; self.size() + 1];
        // Only multiply the bytes that will actually end up in the result value.
        // This is an O(n^2) algorithm at the moment. I think this will be fine for the smaller sized arrays that this
        // will probably be operating on. The largest values this will probably be operating on are 64 byte arrays for
        // a 512-bit SIMD register. The square of that is 4096. That seems like kind of a lot of operations. If that
        // does end up being slow, this should be switched out for a faster multiplication algorithm.
        //
        // Could possible do a runtime switch to using u64s for the elements of the array for a large array like that.
        for i in 0..self.size() {
            let mut carry = 0u8;
            for j in 0..(self.size() - i) {
                let (lo, hi) = self.0[i].carrying_mul(rhs.0[j], carry);
                bytes[i + j] = bytes[i + j].wrapping_add(lo);
                carry = hi;
            }
        }
        bytes.truncate(self.size());
        Big(bytes)
    }
}

impl Not for &Big {
    type Output = Big;

    fn not(self) -> Self::Output {
        let mut bytes = self.0.clone();
        for b in &mut bytes {
            *b = !*b;
        }
        Big(bytes)
    }
}

impl Neg for &Big {
    type Output = Big;

    fn neg(self) -> Self::Output {
        let mut bytes = !self;
        let mut carry = true;
        for b in &mut bytes.0 {
            (*b, carry) = b.carrying_add(0, carry);
            if !carry {
                break;
            }
        }
        bytes
    }
}

impl BitAnd for &Big {
    type Output = Big;

    fn bitand(self, rhs: Self) -> Self::Output {
        debug_assert!(self.size() == rhs.size(), "Must be the same size");
        let mut bytes = Vec::with_capacity(self.size());
        for (a, b) in self.0.iter().zip(rhs.0.iter()) {
            bytes.push(a & b);
        }
        Big(bytes)
    }
}

impl BitOr for &Big {
    type Output = Big;

    fn bitor(self, rhs: Self) -> Self::Output {
        debug_assert!(self.size() == rhs.size(), "Must be the same size");
        let mut bytes = Vec::with_capacity(self.size());
        for (a, b) in self.0.iter().zip(rhs.0.iter()) {
            bytes.push(a | b);
        }
        Big(bytes)
    }
}

impl BitXor for &Big {
    type Output = Big;

    fn bitxor(self, rhs: Self) -> Self::Output {
        debug_assert!(self.size() == rhs.size(), "Must be the same size");
        let mut bytes = Vec::with_capacity(self.size());
        for (a, b) in self.0.iter().zip(rhs.0.iter()) {
            bytes.push(a ^ b);
        }
        Big(bytes)
    }
}

impl PartialEq<[u8]> for Big {
    fn eq(&self, other: &[u8]) -> bool {
        self.0.eq(other)
    }
}

impl PartialEq<[u8]> for &Big {
    fn eq(&self, other: &[u8]) -> bool {
        self.0.eq(other)
    }
}

impl<const N: usize> PartialEq<[u8; N]> for Big {
    fn eq(&self, other: &[u8; N]) -> bool {
        self.0.eq(other)
    }
}

impl<const N: usize> PartialEq<[u8; N]> for &Big {
    fn eq(&self, other: &[u8; N]) -> bool {
        self.0.eq(other)
    }
}

impl PartialOrd<[u8]> for Big {
    fn partial_cmp(&self, other: &[u8]) -> Option<std::cmp::Ordering> {
        let bytes: &[u8] = self.0.as_ref();
        bytes.partial_cmp(other)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn addition() {
        let a: Big = Big::from([0xff, 0x1]);
        let b: Big = Big::from([0x2, 0x3]);
        let c = &a + &b;
        assert_eq!(c, [0x1, 0x5]);
    }

    #[test]
    fn subtraction() {
        let a: Big = Big::from([0xff, 0x1]);
        let b: Big = Big::from([0x2, 0x3]);
        let c = &a - &b;
        assert_eq!(c, [0xfd, 0xfe]);
        let a = Big::from([0x8, 0xa]);
        let b = Big::from([0xa, 0x8]);
        let c = &a - &b;
        assert_eq!(c, [0xfe, 0x1]);
    }

    #[test]
    fn multiplication() {
        let a = Big::from([0x10, 0x00]);
        let b = Big::from([0x10, 0x00]);
        let c = &a * &b;
        assert_eq!(c, [0x00, 0x01]);

        let a = Big::from([0xff, 0xff]);
        let b = Big::from([0xff, 0xff]);
        let c = &a * &b;
        assert_eq!(c, [0x01, 0x00]);
    }

    #[test]
    fn bit_ops() {
        let a: Big = Big::from([0xaa, 0xbb, 0xcc, 0xdd]);
        let b: Big = Big::from([0xff, 0xee, 0x99, 0x76]);
        let and = &a & &b;
        let or = &a | &b;
        let xor = &a ^ &b;
        assert_eq!(and, [0xaa, 0xaa, 0x88, 0x54]);
        assert_eq!(or, [0xff, 0xff, 0xdd, 0xff]);
        assert_eq!(xor, [0x55, 0x55, 0x55, 0xab]);
    }

    #[test]
    fn truncate() {
        let a: Big = Big::from([0xaa, 0xbb, 0xcc, 0xdd, 0xee]);
        let three = a.truncate(3);
        let short = a.truncate(2).get_short();
        let flag = a.truncate(0).get_flag();
        assert_eq!(three.get_big(), [0xaa, 0xbb, 0xcc]);
        assert_eq!(short, 0xbbaa);
        assert_eq!(flag, false);
    }

    #[test]
    fn sign_extend() {
        let unsigned = Big::from([0xaa, 0xbb, 0x01]);
        let signed = Big::from([0x00, 0x01, 0x80]);
        assert_eq!(unsigned.sext(4).get_word(), 0x0001bbaa);
        assert_eq!(signed.sext(4).get_word(), 0xff800100);
        assert_eq!(unsigned.sext(8).get_quad(), 0x0001bbaa);
        assert_eq!(signed.sext(8).get_quad(), 0xffffffffff800100);
        assert_eq!(
            unsigned.sext(9).get_big(),
            [0xaa, 0xbb, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
        );
        assert_eq!(unsigned.sext(9).get_big().size(), 9);
        assert_eq!(
            signed.sext(9).get_big(),
            [0x00, 0x01, 0x80, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
        );
        assert_eq!(signed.sext(9).get_big().size(), 9);
    }

    #[test]
    fn zero_extend() {
        let unsigned = Big::from([0xaa, 0xbb, 0x01]);
        assert_eq!(unsigned.zext(4).get_word(), 0x0001bbaa);
        assert_eq!(unsigned.zext(8).get_quad(), 0x0001bbaa);
        assert_eq!(
            unsigned.zext(9).get_big(),
            [0xaa, 0xbb, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
        );
        assert_eq!(unsigned.zext(9).get_big().size(), 9);
    }

    #[test]
    fn negation() {
        let value = Big::from([0x00, 0xff, 0x01]);
        let not = !&value;
        let neg = -&value;
        assert_eq!(not, [0xff, 0x00, 0xfe]);
        assert_eq!(neg, [0x00, 0x01, 0xfe]);
    }
}
