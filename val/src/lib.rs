//! Values that the emulator will operate on.
//!
//! The main type that the emulator uses is the [`ILVal`]. It supports all of the standard operations that you would
//! expect and can represent any byte-sized value.

use std::fmt::{Debug, Display, LowerHex, UpperHex};
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Rem, Shl, Shr, Sub};

pub mod big;
pub use big::Big;

/// Reference to an [`ILVal`].
///
/// These are registers that can be used for intermediate computations of executing a single architecture level
/// instruction. There can be a maximum of 255 of them, and they are not guaranteed to be preserved between instructions.
#[derive(Clone, Debug, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct ILRef(pub(crate) u8);

impl ILRef {
    /// Get a reference to the next intermediate value.
    pub fn next(&self) -> Self {
        Self(self.0.checked_add(1).expect("Exceeded max ILR index"))
    }
}

/// An intermediate value in some computation.
///
/// This enum will keep track of the size of the current value. It can sign or zero extend to other
/// sizes.
///
/// It implements many arithmetic operations. Only two values of the same size can be used in an
/// operation. Otherwise, the implementation will panic.
#[derive(Clone)]
pub enum ILVal {
    Flag(bool),
    Byte(u8),
    Short(u16),
    Word(u32),
    Quad(u64),
    Big(Big),
}

impl ILVal {
    pub const ZERO: Self = ILVal::Byte(0);

    /// Size of the ILVal in bytes.
    pub fn size(&self) -> usize {
        match self {
            Self::Flag(_) => 0,
            Self::Byte(_) => 1,
            Self::Short(_) => 2,
            Self::Word(_) => 4,
            Self::Quad(_) => 8,
            Self::Big(b) => b.size(),
        }
    }

    /// Convert the value to a u32.
    ///
    /// Will either truncate or zero extend to get a 32 bit value.
    pub fn to_u32(&self) -> u32 {
        match self {
            Self::Flag(v) => *v as u32,
            Self::Byte(v) => *v as u32,
            Self::Short(v) => *v as u32,
            Self::Word(v) => *v,
            Self::Quad(v) => *v as u32,
            Self::Big(_) => unimplemented!("Don't support getting u32 from big integer"),
        }
    }

    /// Convert value to a 64 bit value.
    ///
    /// Will either truncate or zero extend to get a 64 bit value.
    pub fn extend_64(&self) -> u64 {
        match self {
            Self::Flag(b) => *b as u64,
            Self::Byte(b) => *b as u64,
            Self::Short(s) => *s as u64,
            Self::Word(w) => *w as u64,
            Self::Quad(q) => *q,
            Self::Big(_) => unimplemented!("Don't support getting u64 fomr big integer"),
        }
    }

    /// Gets the value if it is a flag and panics otherwise.
    #[inline]
    pub fn get_flag(&self) -> bool {
        if let Self::Flag(b) = self {
            *b
        } else {
            panic!("Value was not a flag")
        }
    }

    /// Gets the value if it is a byte and panics otherwise.
    #[inline]
    pub fn get_byte(&self) -> u8 {
        if let Self::Byte(b) = self {
            *b
        } else {
            panic!("Value was not a byte")
        }
    }

    /// Gets the value if it is a short and panics otherwise.
    #[inline]
    pub fn get_short(&self) -> u16 {
        if let Self::Short(s) = self {
            *s
        } else {
            panic!("Value was not a short")
        }
    }

    /// Gets the value if it is a word and panics otherwise.
    #[inline]
    pub fn get_word(&self) -> u32 {
        if let Self::Word(w) = self {
            *w
        } else {
            panic!("Value was not a word")
        }
    }

    /// Gets the value if it is a quad and panics otherwise.
    #[inline]
    pub fn get_quad(&self) -> u64 {
        if let Self::Quad(q) = self {
            *q
        } else {
            panic!("Value was not a quad")
        }
    }

    /// Gets the value if it is a big integer and panics otherwise.
    pub fn get_big(&self) -> &Big {
        if let Self::Big(b) = self {
            b
        } else {
            panic!("Value was not a big integer")
        }
    }

    /// Checks if the value is true or not.
    ///
    /// This follows the standard c definition of true. So any non-zero value is considered to be true and zero is false.
    pub fn truth(&self) -> bool {
        match self {
            Self::Flag(v) => *v,
            Self::Byte(v) => *v != 0,
            Self::Short(v) => *v != 0,
            Self::Word(v) => *v != 0,
            Self::Quad(v) => *v != 0,
            Self::Big(v) => v.truth(),
        }
    }

    /// Rotate right operation.
    pub fn rotate_right(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Byte(l), Self::Byte(r)) => Self::Byte(l.rotate_right(*r as u32)),
            (Self::Short(l), Self::Byte(r)) => Self::Short(l.rotate_right(*r as u32)),
            (Self::Short(l), Self::Short(r)) => Self::Short(l.rotate_right(*r as u32)),
            (Self::Word(l), Self::Byte(r)) => Self::Word(l.rotate_right(*r as u32)),
            (Self::Word(l), Self::Short(r)) => Self::Word(l.rotate_right(*r as u32)),
            (Self::Word(l), Self::Word(r)) => Self::Word(l.rotate_right(*r as u32)),
            (Self::Quad(l), Self::Byte(r)) => Self::Quad(l.rotate_right(*r as u32)),
            (Self::Quad(l), Self::Short(r)) => Self::Quad(l.rotate_right(*r as u32)),
            (Self::Quad(l), Self::Word(r)) => Self::Quad(l.rotate_right(*r as u32)),
            (Self::Quad(l), Self::Quad(r)) => Self::Quad(l.rotate_right(*r as u32)),
            (_, _) => unreachable!("Invalid combination for rotate right"),
        }
    }

    /// Arithmetic shift right operation.
    ///
    /// Just a right shift but as a signed value.
    pub fn asr(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Byte(l), Self::Byte(r)) => {
                Self::Byte(((*l as i8).unbounded_shr((r & 7) as u32)) as u8)
            }
            (Self::Short(l), Self::Byte(r)) => {
                Self::Short(((*l as i16).unbounded_shr((r & 15) as u32)) as u16)
            }
            (Self::Short(l), Self::Short(r)) => {
                Self::Short(((*l as i16).unbounded_shr((r & 15) as u32)) as u16)
            }
            (Self::Word(l), Self::Byte(r)) => {
                Self::Word(((*l as i32).unbounded_shr((r & 31) as u32)) as u32)
            }
            (Self::Word(l), Self::Short(r)) => {
                Self::Word(((*l as i32).unbounded_shr((r & 31) as u32)) as u32)
            }
            (Self::Word(l), Self::Word(r)) => {
                Self::Word(((*l as i32).unbounded_shr((r & 31) as u32)) as u32)
            }
            (Self::Quad(l), Self::Byte(r)) => {
                Self::Quad(((*l as i64).unbounded_shr((r & 63) as u32)) as u64)
            }
            (Self::Quad(l), Self::Short(r)) => {
                Self::Quad(((*l as i64).unbounded_shr((r & 63) as u32)) as u64)
            }
            (Self::Quad(l), Self::Word(r)) => {
                Self::Quad(((*l as i64).unbounded_shr((r & 63) as u32)) as u64)
            }
            (Self::Quad(l), Self::Quad(r)) => {
                Self::Quad(((*l as i64).unbounded_shr((r & 63) as u32)) as u64)
            }
            (_, _) => unreachable!("Invalid combination for rotate right"),
        }
    }

    /// Treat the values as signed and compare them.
    pub fn signed_cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Self::Byte(v1), Self::Byte(v2)) => {
                let v1 = *v1 as i8;
                let v2 = *v2 as i8;
                v1.cmp(&v2)
            }
            (Self::Short(v1), Self::Short(v2)) => {
                let v1 = *v1 as i16;
                let v2 = *v2 as i16;
                v1.cmp(&v2)
            }
            (Self::Word(v1), Self::Word(v2)) => {
                let v1 = *v1 as i32;
                let v2 = *v2 as i32;
                v1.cmp(&v2)
            }
            (Self::Quad(v1), Self::Quad(v2)) => {
                let v1 = *v1 as i64;
                let v2 = *v2 as i64;
                v1.cmp(&v2)
            }
            (_, _) => unreachable!("Different sized ILVals in signed comparison"),
        }
    }

    /// Treat values as signed and divide them.
    ///
    /// # Panics
    /// Two values must be of the same size.
    pub fn signed_div(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Byte(v1), Self::Byte(v2)) => {
                Self::Byte((*v1 as i8).wrapping_div(*v2 as i8) as u8)
            }
            (Self::Short(v1), Self::Short(v2)) => {
                Self::Short((*v1 as i16).wrapping_div(*v2 as i16) as u16)
            }
            (Self::Word(v1), Self::Word(v2)) => {
                Self::Word((*v1 as i32).wrapping_div(*v2 as i32) as u32)
            }
            (Self::Quad(v1), Self::Quad(v2)) => {
                Self::Quad((*v1 as i64).wrapping_div(*v2 as i64) as u64)
            }
            (_, _) => unreachable!("Invalid combination for signed division"),
        }
    }

    /// Truncate the value to a specific size.
    ///
    /// # Panics
    /// `size` must be one of 1, 2, 4, or 8 and that size must be smaller than
    /// the current size of the value.
    pub fn truncate(&self, size: u8) -> Self {
        match (self, size) {
            (Self::Byte(v), 1) => Self::Byte(*v),
            (Self::Short(v), 1) => Self::Byte(*v as u8),
            (Self::Short(v), 2) => Self::Short(*v),
            (Self::Word(w), 1) => Self::Byte(*w as u8),
            (Self::Word(w), 2) => Self::Short(*w as u16),
            (Self::Word(v), 4) => Self::Word(*v),
            (Self::Quad(q), 1) => Self::Byte(*q as u8),
            (Self::Quad(q), 2) => Self::Short(*q as u16),
            (Self::Quad(q), 4) => Self::Word(*q as u32),
            (Self::Quad(v), 8) => Self::Quad(*v),
            (Self::Big(b), s) => b.truncate(s),
            (_, _) => unreachable!("Invalid truncation combination: {self:?} => {size}"),
        }
    }

    /// Sign extend to a specific size.
    ///
    /// # Panics
    /// `size` must be one of 1, 2, 4, or 8 and that size must be larger than
    /// the current size of the value.
    pub fn sext(&self, size: u8) -> Self {
        match (self, size) {
            (Self::Byte(v), 1) => Self::Byte(*v),
            (Self::Byte(v), 2) => Self::Short(*v as i8 as i16 as u16),
            (Self::Byte(v), 4) => Self::Word(*v as i8 as i32 as u32),
            (Self::Byte(v), 8) => Self::Quad(*v as i8 as i64 as u64),
            (Self::Short(v), 2) => Self::Short(*v),
            (Self::Short(v), 4) => Self::Word(*v as i16 as i32 as u32),
            (Self::Short(v), 8) => Self::Quad(*v as i16 as i64 as u64),
            (Self::Word(v), 4) => Self::Word(*v),
            (Self::Word(v), 8) => Self::Quad(*v as i32 as i64 as u64),
            (Self::Big(b), s) => b.sext(s),
            (_, _) => unreachable!("Invalid sign extension combination"),
        }
    }

    /// Zero extend to a specific size.
    ///
    /// # Panics
    /// `size` must be one of 1, 2, 4, or 8 and that size must be larger than
    /// the current size of the value.
    pub fn zext(&self, size: u8) -> Self {
        match (self, size) {
            (Self::Byte(v), 1) => Self::Byte(*v),
            (Self::Byte(v), 2) => Self::Short(*v as u16),
            (Self::Byte(v), 4) => Self::Word(*v as u32),
            (Self::Byte(v), 8) => Self::Quad(*v as u64),
            (Self::Short(v), 2) => Self::Short(*v),
            (Self::Short(v), 4) => Self::Word(*v as u32),
            (Self::Short(v), 8) => Self::Quad(*v as u64),
            (Self::Word(v), 4) => Self::Word(*v),
            (Self::Word(v), 8) => Self::Quad(*v as u64),
            (Self::Quad(v), 8) => Self::Quad(*v),
            (Self::Big(b), s) => b.zext(s),
            (_, _) => unreachable!("Invalid zero extension combination {self:?} -> {size}"),
        }
    }

    /// Zero extend value then multiply.
    pub fn mulu_dp(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Word(left), Self::Word(right)) => {
                Self::Quad((*left as u64).wrapping_mul(*right as u64))
            }
            (Self::Quad(left), Self::Quad(right)) => {
                let mul = (*left as u128).wrapping_mul(*right as u128);
                Self::Big(Big::from(mul.to_le_bytes()))
            }
            (_, _) => unreachable!("Invalid combo of {:?} and {:?}", self, other),
        }
    }

    /// Sign extend value then multiply
    pub fn muls_dp(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Word(left), Self::Word(right)) => {
                Self::Quad((*left as i32 as i64).wrapping_mul(*right as i32 as i64) as u64)
            }
            (Self::Quad(left), Self::Quad(right)) => {
                let mul = (*left as i64 as i128).wrapping_mul(*right as i64 as i128);
                Self::Big(Big::from(mul.to_le_bytes()))
            }
            (_, _) => unreachable!("Invalid combo of {:?} and {:?}", self, other),
        }
    }

    /// Bit-wise reversal of value.
    pub fn bit_rev(&self) -> Self {
        match self {
            Self::Flag(v) => Self::Flag(*v),
            Self::Byte(v) => Self::Byte(v.reverse_bits()),
            Self::Short(v) => Self::Short(v.reverse_bits()),
            Self::Word(v) => Self::Word(v.reverse_bits()),
            Self::Quad(v) => Self::Quad(v.reverse_bits()),
            Self::Big(v) => Self::Big(v.bit_reverse()),
        }
    }

    /// Byte-wise reversal of value.
    pub fn byte_rev(&self) -> Self {
        match self {
            Self::Flag(v) => Self::Flag(*v),
            Self::Byte(v) => Self::Byte(v.swap_bytes()),
            Self::Short(v) => Self::Short(v.swap_bytes()),
            Self::Word(v) => Self::Word(v.swap_bytes()),
            Self::Quad(v) => Self::Quad(v.swap_bytes()),
            Self::Big(v) => Self::Big(v.byte_reverse()),
        }
    }

    /// Leading zeros.
    pub fn leading_zeros(&self) -> Self {
        match self {
            Self::Byte(v) => Self::Word(v.leading_zeros()),
            Self::Short(v) => Self::Word(v.leading_zeros()),
            Self::Word(v) => Self::Word(v.leading_zeros()),
            Self::Quad(v) => Self::Word(v.leading_zeros()),
            x => panic!("{x:?} does not support leading zeros"),
        }
    }

    /// Check if an add would overflow or not.
    pub fn add_of(&self, other: &Self) -> Self {
        // TODO: This might be architecture specific. It seems like this should be signed addition checking overflow.
        match (self, other) {
            (Self::Byte(a), Self::Byte(b)) => Self::Flag((*a as i8).overflowing_sub(*b as i8).1),
            (Self::Short(a), Self::Byte(b)) => Self::Flag(a.overflowing_sub(*b as u16).1),
            (Self::Short(a), Self::Short(b)) => Self::Flag(a.overflowing_sub(*b).1),
            (Self::Word(a), Self::Byte(b)) => Self::Flag(a.overflowing_sub(*b as u32).1),
            (Self::Word(a), Self::Short(b)) => Self::Flag(a.overflowing_sub(*b as u32).1),
            (Self::Word(a), Self::Word(b)) => Self::Flag((*a as i32).overflowing_sub(*b as i32).1),
            (Self::Quad(a), Self::Byte(b)) => Self::Flag(a.overflowing_sub(*b as u64).1),
            (Self::Quad(a), Self::Short(b)) => Self::Flag(a.overflowing_sub(*b as u64).1),
            (Self::Quad(a), Self::Word(b)) => Self::Flag(a.overflowing_sub(*b as u64).1),
            (Self::Quad(a), Self::Quad(b)) => Self::Flag((a).overflowing_sub(*b).1),
            _ => panic!("Trying to check overflow of unsupported types: {self:?} + {other:?}"),
        }
    }
}

impl Debug for ILVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Flag(b) => write!(f, "{b}"),
            Self::Byte(b) => write!(f, "{:X}b", b),
            Self::Short(s) => write!(f, "{:X}s", s),
            Self::Word(w) => write!(f, "{:X}w", w),
            Self::Quad(q) => write!(f, "{:X}q", q),
            Self::Big(b) => write!(f, "{:?}", b),
        }
    }
}

impl Display for ILVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Flag(b) => write!(f, "{b}"),
            Self::Byte(b) => write!(f, "{:X}", b),
            Self::Short(s) => write!(f, "{:X}", s),
            Self::Word(w) => write!(f, "{:X}", w),
            Self::Quad(q) => write!(f, "{:X}", q),
            Self::Big(b) => write!(f, "{:?}", b),
        }
    }
}

impl LowerHex for ILVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Flag(v) => LowerHex::fmt(if *v { &1 } else { &0 }, f),
            Self::Byte(v) => LowerHex::fmt(v, f),
            Self::Short(v) => LowerHex::fmt(v, f),
            Self::Word(v) => LowerHex::fmt(v, f),
            Self::Quad(v) => LowerHex::fmt(v, f),
            Self::Big(b) => LowerHex::fmt(b, f),
        }
    }
}

impl UpperHex for ILVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Flag(v) => UpperHex::fmt(if *v { &1 } else { &0 }, f),
            Self::Byte(v) => UpperHex::fmt(v, f),
            Self::Short(v) => UpperHex::fmt(v, f),
            Self::Word(v) => UpperHex::fmt(v, f),
            Self::Quad(v) => UpperHex::fmt(v, f),
            Self::Big(v) => UpperHex::fmt(v, f),
        }
    }
}

impl ILVal {}

impl PartialEq for ILVal {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Flag(b1), Self::Flag(b2)) => b1 == b2,
            (Self::Byte(b1), Self::Byte(b2)) => b1 == b2,
            (Self::Short(s1), Self::Short(s2)) => s1 == s2,
            (Self::Word(w1), Self::Word(w2)) => w1 == w2,
            (Self::Quad(q1), Self::Quad(q2)) => q1 == q2,
            (Self::Big(b1), Self::Big(b2)) => b1 == b2,
            (_, _) => false,
        }
    }
}

impl Eq for ILVal {}

impl PartialOrd for ILVal {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Self::Flag(b1), Self::Flag(b2)) => b1.partial_cmp(b2),
            (Self::Byte(b1), Self::Byte(b2)) => b1.partial_cmp(b2),
            (Self::Short(s1), Self::Short(s2)) => s1.partial_cmp(s2),
            (Self::Word(w1), Self::Word(w2)) => w1.partial_cmp(w2),
            (Self::Quad(q1), Self::Quad(q2)) => q1.partial_cmp(q2),
            (Self::Big(b1), Self::Big(b2)) => b1.partial_cmp(b2),
            (_, _) => panic!("Comparing types of unequal size"),
        }
    }
}

impl From<bool> for ILVal {
    fn from(value: bool) -> Self {
        Self::Flag(value)
    }
}

impl From<u8> for ILVal {
    fn from(val: u8) -> Self {
        Self::Byte(val)
    }
}

impl From<i8> for ILVal {
    fn from(val: i8) -> Self {
        Self::Byte(val as u8)
    }
}

impl From<u16> for ILVal {
    fn from(val: u16) -> Self {
        Self::Short(val)
    }
}

impl From<i16> for ILVal {
    fn from(val: i16) -> Self {
        Self::Short(val as u16)
    }
}

impl From<u32> for ILVal {
    fn from(val: u32) -> Self {
        Self::Word(val)
    }
}

impl From<i32> for ILVal {
    fn from(val: i32) -> Self {
        Self::Word(val as u32)
    }
}

impl From<u64> for ILVal {
    fn from(val: u64) -> Self {
        Self::Quad(val)
    }
}

impl From<i64> for ILVal {
    fn from(val: i64) -> Self {
        Self::Quad(val as u64)
    }
}

impl From<u128> for ILVal {
    fn from(value: u128) -> Self {
        Self::Big(Big::from(value.to_le_bytes()))
    }
}

impl From<i128> for ILVal {
    fn from(value: i128) -> Self {
        Self::Big(Big::from(value.to_le_bytes()))
    }
}

impl From<f32> for ILVal {
    fn from(value: f32) -> Self {
        Self::Word(value as u32)
    }
}

impl From<f64> for ILVal {
    fn from(value: f64) -> Self {
        Self::Quad(value as u64)
    }
}

impl Add for &ILVal {
    type Output = ILVal;

    /// Wrapping add of two ILVals.
    ///
    /// # Panics
    /// ILVals must have the same size or this will panic.
    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (ILVal::Byte(a), ILVal::Byte(b)) => ILVal::Byte(a.wrapping_add(*b)),
            (ILVal::Short(a), ILVal::Byte(b)) => ILVal::Short(a.wrapping_add(*b as u16)),
            (ILVal::Short(a), ILVal::Short(b)) => ILVal::Short(a.wrapping_add(*b)),
            (ILVal::Word(a), ILVal::Byte(b)) => ILVal::Word(a.wrapping_add(*b as u32)),
            (ILVal::Word(a), ILVal::Short(b)) => ILVal::Word(a.wrapping_add(*b as u32)),
            (ILVal::Word(a), ILVal::Word(b)) => ILVal::Word(a.wrapping_add(*b)),
            (ILVal::Quad(a), ILVal::Byte(b)) => ILVal::Quad(a.wrapping_add(*b as u64)),
            (ILVal::Quad(a), ILVal::Short(b)) => ILVal::Quad(a.wrapping_add(*b as u64)),
            (ILVal::Quad(a), ILVal::Word(b)) => ILVal::Quad(a.wrapping_add(*b as u64)),
            (ILVal::Quad(a), ILVal::Quad(b)) => ILVal::Quad(a.wrapping_add(*b)),
            (ILVal::Big(a), ILVal::Big(b)) => ILVal::Big(a + b),
            _ => panic!("Trying to add different sized integers: {self:?} + {rhs:?}"),
        }
    }
}

impl Sub for &ILVal {
    type Output = ILVal;

    /// Wrapping subtraction of two ILVals.
    ///
    /// # Panics
    /// ILVals must have the same size or this will panic.
    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (ILVal::Byte(a), ILVal::Byte(b)) => ILVal::Byte(a.wrapping_sub(*b)),
            (ILVal::Short(a), ILVal::Short(b)) => ILVal::Short(a.wrapping_sub(*b)),
            (ILVal::Word(a), ILVal::Word(b)) => ILVal::Word(a.wrapping_sub(*b)),
            (ILVal::Quad(a), ILVal::Quad(b)) => ILVal::Quad(a.wrapping_sub(*b)),
            (ILVal::Big(a), ILVal::Big(b)) => ILVal::Big(a - b),
            _ => panic!("Trying to subtract different sized integers"),
        }
    }
}

impl Mul for &ILVal {
    type Output = ILVal;

    /// Wrapping multiply of two ILVals.
    ///
    /// # Panics
    /// ILVals must have the same size or this will panic.
    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (ILVal::Byte(a), ILVal::Byte(b)) => ILVal::Byte(a.wrapping_mul(*b)),
            (ILVal::Short(a), ILVal::Short(b)) => ILVal::Short(a.wrapping_mul(*b)),
            (ILVal::Word(a), ILVal::Word(b)) => ILVal::Word(a.wrapping_mul(*b)),
            (ILVal::Quad(a), ILVal::Quad(b)) => ILVal::Quad(a.wrapping_mul(*b)),
            (ILVal::Big(a), ILVal::Big(b)) => ILVal::Big(a * b),
            _ => panic!("Trying to multiply different sized integers"),
        }
    }
}

impl Div for &ILVal {
    type Output = ILVal;

    /// Wrapping division of two ILVals.
    ///
    /// # Panics
    /// ILVals must have the same size.
    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (ILVal::Byte(a), ILVal::Byte(b)) => ILVal::Byte(a.wrapping_div(*b)),
            (ILVal::Short(a), ILVal::Short(b)) => ILVal::Short(a.wrapping_div(*b)),
            (ILVal::Word(a), ILVal::Word(b)) => ILVal::Word(a.wrapping_div(*b)),
            (ILVal::Quad(a), ILVal::Quad(b)) => ILVal::Quad(a.wrapping_div(*b)),
            _ => panic!("Trying to divide different sized integers"),
        }
    }
}

impl BitAnd for &ILVal {
    type Output = ILVal;

    fn bitand(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (ILVal::Flag(a), ILVal::Flag(b)) => ILVal::Flag(a & b),
            (ILVal::Byte(a), ILVal::Byte(b)) => ILVal::Byte(a & b),
            (ILVal::Short(a), ILVal::Short(b)) => ILVal::Short(a & b),
            (ILVal::Word(a), ILVal::Word(b)) => ILVal::Word(a & b),
            (ILVal::Quad(a), ILVal::Quad(b)) => ILVal::Quad(a & b),
            (ILVal::Big(a), ILVal::Big(b)) => ILVal::Big(a & b),
            _ => panic!("Trying to bitwise and different sized integers"),
        }
    }
}

impl BitOr for &ILVal {
    type Output = ILVal;

    fn bitor(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (ILVal::Flag(a), ILVal::Flag(b)) => ILVal::Flag(*a || *b),
            (ILVal::Byte(a), ILVal::Byte(b)) => ILVal::Byte(a | b),
            (ILVal::Short(a), ILVal::Short(b)) => ILVal::Short(a | b),
            (ILVal::Word(a), ILVal::Word(b)) => ILVal::Word(a | b),
            (ILVal::Quad(a), ILVal::Quad(b)) => ILVal::Quad(a | b),
            (ILVal::Big(a), ILVal::Big(b)) => ILVal::Big(a | b),
            _ => panic!("Trying to bitwise or different sized integers"),
        }
    }
}

impl BitXor for &ILVal {
    type Output = ILVal;

    fn bitxor(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (ILVal::Byte(a), ILVal::Byte(b)) => ILVal::Byte(a ^ b),
            (ILVal::Short(a), ILVal::Short(b)) => ILVal::Short(a ^ b),
            (ILVal::Word(a), ILVal::Word(b)) => ILVal::Word(a ^ b),
            (ILVal::Quad(a), ILVal::Quad(b)) => ILVal::Quad(a ^ b),
            (ILVal::Big(a), ILVal::Big(b)) => ILVal::Big(a ^ b),
            _ => panic!("Trying to bitwise xor different sized integers"),
        }
    }
}

impl Neg for &ILVal {
    type Output = ILVal;

    fn neg(self) -> Self::Output {
        match self {
            ILVal::Flag(v) => ILVal::Flag(!v),
            ILVal::Byte(v) => ILVal::Byte(-(*v as i8) as u8),
            ILVal::Short(v) => ILVal::Short(-(*v as i16) as u16),
            ILVal::Word(v) => ILVal::Word(-(*v as i32) as u32),
            ILVal::Quad(v) => ILVal::Quad(-(*v as i64) as u64),
            ILVal::Big(v) => ILVal::Big(-v),
        }
    }
}

impl Not for &ILVal {
    type Output = ILVal;

    fn not(self) -> Self::Output {
        match self {
            ILVal::Flag(v) => ILVal::Flag(!v),
            ILVal::Byte(v) => ILVal::Byte(!v),
            ILVal::Short(v) => ILVal::Short(!v),
            ILVal::Word(v) => ILVal::Word(!v),
            ILVal::Quad(v) => ILVal::Quad(!v),
            ILVal::Big(v) => ILVal::Big(!v),
        }
    }
}

impl Rem for &ILVal {
    type Output = ILVal;

    fn rem(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (ILVal::Byte(l), ILVal::Byte(r)) => ILVal::Byte(l.wrapping_rem(*r)),
            (ILVal::Short(l), ILVal::Short(r)) => ILVal::Short(l.wrapping_rem(*r)),
            (ILVal::Word(l), ILVal::Word(r)) => ILVal::Word(l.wrapping_rem(*r)),
            (ILVal::Quad(l), ILVal::Quad(r)) => ILVal::Quad(l.wrapping_rem(*r)),
            _ => panic!("Incompatible sizes for remainder operation"),
        }
    }
}

impl Shl for &ILVal {
    type Output = ILVal;

    fn shl(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (ILVal::Byte(l), ILVal::Byte(r)) => ILVal::Byte(l.unbounded_shl((*r & 7) as u32)),
            (ILVal::Short(l), ILVal::Byte(r)) => ILVal::Short(l.unbounded_shl((*r & 15) as u32)),
            (ILVal::Short(l), ILVal::Short(r)) => ILVal::Short(l.unbounded_shl((*r & 15) as u32)),
            (ILVal::Word(l), ILVal::Byte(r)) => ILVal::Word(l.unbounded_shl((*r & 31) as u32)),
            (ILVal::Word(l), ILVal::Short(r)) => ILVal::Word(l.unbounded_shl((*r & 31) as u32)),
            (ILVal::Word(l), ILVal::Word(r)) => ILVal::Word(l.unbounded_shl((*r & 31) as u32)),
            (ILVal::Quad(l), ILVal::Byte(r)) => ILVal::Quad(l.unbounded_shl((*r & 63) as u32)),
            (ILVal::Quad(l), ILVal::Short(r)) => ILVal::Quad(l.unbounded_shl((*r & 63) as u32)),
            (ILVal::Quad(l), ILVal::Word(r)) => ILVal::Quad(l.unbounded_shl((*r & 63) as u32)),
            (ILVal::Quad(l), ILVal::Quad(r)) => ILVal::Quad(l.unbounded_shl((*r & 63) as u32)),
            _ => panic!("Incompatible sizes for shift left operation"),
        }
    }
}

impl Shr for &ILVal {
    type Output = ILVal;

    fn shr(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (ILVal::Byte(l), ILVal::Byte(r)) => ILVal::Byte(l.unbounded_shr((*r & 7) as u32)),
            (ILVal::Short(l), ILVal::Byte(r)) => ILVal::Short(l.unbounded_shr((*r & 15) as u32)),
            (ILVal::Short(l), ILVal::Short(r)) => ILVal::Short(l.unbounded_shr((*r & 15) as u32)),
            (ILVal::Word(l), ILVal::Byte(r)) => ILVal::Word(l.unbounded_shr((*r & 31) as u32)),
            (ILVal::Word(l), ILVal::Short(r)) => ILVal::Word(l.unbounded_shr((*r & 31) as u32)),
            (ILVal::Word(l), ILVal::Word(r)) => ILVal::Word(l.unbounded_shr((*r & 31) as u32)),
            (ILVal::Quad(l), ILVal::Byte(r)) => ILVal::Quad(l.unbounded_shr((*r & 63) as u32)),
            (ILVal::Quad(l), ILVal::Short(r)) => ILVal::Quad(l.unbounded_shr((*r & 63) as u32)),
            (ILVal::Quad(l), ILVal::Word(r)) => ILVal::Quad(l.unbounded_shr((*r & 63) as u32)),
            (ILVal::Quad(l), ILVal::Quad(r)) => ILVal::Quad(l.unbounded_shr((*r & 63) as u32)),
            _ => panic!("Incompatible sizes for shift right operation"),
        }
    }
}
