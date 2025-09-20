//! Emil (EMulation Intermediate Language) is the intermediate language that will get executed during
//! emulation.
//!
//! Emil is essentially just a linear version of Binary Ninja's low level intermediate language (LLIL).
//! LLIL is parsed into an abstract syntax tree representation. That representation works well for
//! representing the semantics of the binary but is not ideal for emulation. Traversing the AST
//! requires some amount of recursive descent which will hurt the performance of the hot loop that
//! just fetches and executes an instruction.
//!
//! Emil is a transformation of LLIL into a linear form. It treats all LLIL instructions and
//! expressions as operations that operate on an ['ILVal`] which represents some value in the
//! machines state. Each LLIL instruction and expression will be transformed to operate on the ILVals
//! so that each instruction can be executed independently of any other instruction.
//!
//! Instructions only operate on the ILVals so any value that is required by an instruction needs to
//! first be loaded into an ILVal. In this way, reading and writing registers or memory is
//! essentially just treated as a side effect of the instruction.

use crate::arch::{Register as Reg, State};
use crate::emulate::{Endian, HookStatus};
use std::fmt::{Debug, Display, LowerHex, UpperHex};
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Rem, Shl, Shr, Sub};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Reference to an [`ILVal`].
///
/// These are registers that can be used for intermediate computations of executing a single architecture level
/// instruction. There can be a maximum of 255 of them, and they are not guaranteed to be preserved between instructions.
#[derive(Clone, Debug, Copy, PartialEq, Eq)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
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
#[derive(Clone, Copy)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum ILVal {
    Byte(u8),
    Short(u16),
    Word(u32),
    Quad(u64),
}

impl ILVal {
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
    pub fn signed_div(self, other: Self) -> Self {
        match (self, other) {
            (Self::Byte(v1), Self::Byte(v2)) => Self::Byte(((v1 as i8) / (v2 as i8)) as u8),
            (Self::Short(v1), Self::Short(v2)) => Self::Short(((v1 as i16) / (v2 as i16)) as u16),
            (Self::Word(v1), Self::Word(v2)) => Self::Word(((v1 as i32) / (v2 as i32)) as u32),
            (Self::Quad(v1), Self::Quad(v2)) => Self::Quad(((v1 as i64) / (v2 as i64)) as u64),
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
            (Self::Short(v), 1) => Self::Byte(*v as u8),
            (Self::Word(w), 1) => Self::Byte(*w as u8),
            (Self::Word(w), 2) => Self::Short(*w as u16),
            (Self::Quad(q), 1) => Self::Byte(*q as u8),
            (Self::Quad(q), 2) => Self::Short(*q as u16),
            (Self::Quad(q), 4) => Self::Word(*q as u32),
            (_, _) => unreachable!("Invalid truncation combination"),
        }
    }

    /// Sign extend to a specific size.
    ///
    /// # Panics
    /// `size` must be one of 1, 2, 4, or 8 and that size must be larger than
    /// the current size of the value.
    pub fn sext(&self, size: u8) -> Self {
        match (self, size) {
            (Self::Byte(v), 2) => Self::Short(*v as i8 as i16 as u16),
            (Self::Byte(v), 4) => Self::Word(*v as i8 as i32 as u32),
            (Self::Byte(v), 8) => Self::Quad(*v as i8 as i64 as u64),
            (Self::Short(v), 4) => Self::Word(*v as i16 as i32 as u32),
            (Self::Short(v), 8) => Self::Quad(*v as i16 as i64 as u64),
            (Self::Word(v), 8) => Self::Quad(*v as i32 as i64 as u64),
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
            (Self::Byte(v), 2) => Self::Short(*v as u16),
            (Self::Byte(v), 4) => Self::Word(*v as u32),
            (Self::Byte(v), 8) => Self::Quad(*v as u64),
            (Self::Short(v), 4) => Self::Word(*v as u32),
            (Self::Short(v), 8) => Self::Quad(*v as u64),
            (Self::Word(v), 8) => Self::Quad(*v as u64),
            (_, _) => unreachable!("Invalid sign extension combination"),
        }
    }
}

impl Debug for ILVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Byte(b) => write!(f, "{:X}b", b),
            Self::Short(s) => write!(f, "{:X}s", s),
            Self::Word(w) => write!(f, "{:X}w", w),
            Self::Quad(q) => write!(f, "{:X}q", q),
        }
    }
}

impl Display for ILVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Byte(b) => write!(f, "{:X}", b),
            Self::Short(s) => write!(f, "{:X}", s),
            Self::Word(w) => write!(f, "{:X}", w),
            Self::Quad(q) => write!(f, "{:X}", q),
        }
    }
}

impl LowerHex for ILVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Byte(v) => LowerHex::fmt(v, f),
            Self::Short(v) => LowerHex::fmt(v, f),
            Self::Word(v) => LowerHex::fmt(v, f),
            Self::Quad(v) => LowerHex::fmt(v, f),
        }
    }
}

impl UpperHex for ILVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Byte(v) => UpperHex::fmt(v, f),
            Self::Short(v) => UpperHex::fmt(v, f),
            Self::Word(v) => UpperHex::fmt(v, f),
            Self::Quad(v) => UpperHex::fmt(v, f),
        }
    }
}

impl ILVal {
    pub fn extend_64(&self) -> u64 {
        match self {
            Self::Byte(b) => *b as u64,
            Self::Short(s) => *s as u64,
            Self::Word(w) => *w as u64,
            Self::Quad(q) => *q,
        }
    }
}

impl PartialEq for ILVal {
    fn eq(&self, other: &Self) -> bool {
        match (*self, *other) {
            (Self::Byte(b1), Self::Byte(b2)) => b1 == b2,
            (Self::Short(s1), Self::Short(s2)) => s1 == s2,
            (Self::Word(w1), Self::Word(w2)) => w1 == w2,
            (Self::Quad(q1), Self::Quad(q2)) => q1 == q2,
            (_, _) => false,
        }
    }
}

impl Eq for ILVal {}

impl PartialOrd for ILVal {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (*self, *other) {
            (Self::Byte(b1), Self::Byte(b2)) => b1.partial_cmp(&b2),
            (Self::Short(s1), Self::Short(s2)) => s1.partial_cmp(&s2),
            (Self::Word(w1), Self::Word(w2)) => w1.partial_cmp(&w2),
            (Self::Quad(q1), Self::Quad(q2)) => q1.partial_cmp(&q2),
            (_, _) => panic!("Comparing types of unequal size"),
        }
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

impl Add for ILVal {
    type Output = Self;

    /// Wrapping add of two ILVals.
    ///
    /// # Panics
    /// ILVals must have the same size or this will panic.
    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Byte(a), Self::Byte(b)) => Self::Byte(a.wrapping_add(b)),
            (Self::Short(a), Self::Short(b)) => Self::Short(a.wrapping_add(b)),
            (Self::Word(a), Self::Word(b)) => Self::Word(a.wrapping_add(b)),
            (Self::Quad(a), Self::Quad(b)) => Self::Quad(a.wrapping_add(b)),
            _ => panic!("Trying to add different sized integers"),
        }
    }
}

impl Sub for ILVal {
    type Output = Self;

    /// Wrapping subtraction of two ILVals.
    ///
    /// # Panics
    /// ILVals must have the same size or this will panic.
    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Byte(a), Self::Byte(b)) => Self::Byte(a.wrapping_sub(b)),
            (Self::Short(a), Self::Short(b)) => Self::Short(a.wrapping_sub(b)),
            (Self::Word(a), Self::Word(b)) => Self::Word(a.wrapping_sub(b)),
            (Self::Quad(a), Self::Quad(b)) => Self::Quad(a.wrapping_sub(b)),
            _ => panic!("Trying to subtract different sized integers"),
        }
    }
}

impl Mul for ILVal {
    type Output = Self;

    /// Wrapping multiply of two ILVals.
    ///
    /// # Panics
    /// ILVals must have the same size or this will panic.
    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Byte(a), Self::Byte(b)) => Self::Byte(a.wrapping_mul(b)),
            (Self::Short(a), Self::Short(b)) => Self::Short(a.wrapping_mul(b)),
            (Self::Word(a), Self::Word(b)) => Self::Word(a.wrapping_mul(b)),
            (Self::Quad(a), Self::Quad(b)) => Self::Quad(a.wrapping_mul(b)),
            _ => panic!("Trying to multiply different sized integers"),
        }
    }
}

impl Div for ILVal {
    type Output = Self;

    /// Wrapping division of two ILVals.
    ///
    /// # Panics
    /// ILVals must have the same size.
    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Byte(a), Self::Byte(b)) => Self::Byte(a.wrapping_div(b)),
            (Self::Short(a), Self::Short(b)) => Self::Short(a.wrapping_div(b)),
            (Self::Word(a), Self::Word(b)) => Self::Word(a.wrapping_div(b)),
            (Self::Quad(a), Self::Quad(b)) => Self::Quad(a.wrapping_div(b)),
            _ => panic!("Trying to divide different sized integers"),
        }
    }
}

impl BitAnd for ILVal {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Byte(a), Self::Byte(b)) => Self::Byte(a & b),
            (Self::Short(a), Self::Short(b)) => Self::Short(a & b),
            (Self::Word(a), Self::Word(b)) => Self::Word(a & b),
            (Self::Quad(a), Self::Quad(b)) => Self::Quad(a & b),
            _ => panic!("Trying to bitwise and different sized integers"),
        }
    }
}

impl BitOr for ILVal {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Byte(a), Self::Byte(b)) => Self::Byte(a | b),
            (Self::Short(a), Self::Short(b)) => Self::Short(a | b),
            (Self::Word(a), Self::Word(b)) => Self::Word(a | b),
            (Self::Quad(a), Self::Quad(b)) => Self::Quad(a | b),
            _ => panic!("Trying to bitwise or different sized integers"),
        }
    }
}

impl BitXor for ILVal {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Byte(a), Self::Byte(b)) => Self::Byte(a ^ b),
            (Self::Short(a), Self::Short(b)) => Self::Short(a ^ b),
            (Self::Word(a), Self::Word(b)) => Self::Word(a ^ b),
            (Self::Quad(a), Self::Quad(b)) => Self::Quad(a ^ b),
            _ => panic!("Trying to bitwise xor different sized integers"),
        }
    }
}

impl Neg for ILVal {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Self::Byte(b) => Self::Byte(-(b as i8) as u8),
            Self::Short(b) => Self::Short(-(b as i16) as u16),
            Self::Word(b) => Self::Word(-(b as i32) as u32),
            Self::Quad(b) => Self::Quad(-(b as i64) as u64),
        }
    }
}

impl Not for ILVal {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Self::Byte(b) => Self::Byte(!b),
            Self::Short(b) => Self::Short(!b),
            Self::Word(b) => Self::Word(!b),
            Self::Quad(b) => Self::Quad(!b),
        }
    }
}

impl Rem for ILVal {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Byte(l), Self::Byte(r)) => Self::Byte(l % r),
            (Self::Short(l), Self::Short(r)) => Self::Short(l % r),
            (Self::Word(l), Self::Word(r)) => Self::Word(l % r),
            (Self::Quad(l), Self::Quad(r)) => Self::Quad(l % r),
            _ => panic!("Incompatible sizes for remainder operation"),
        }
    }
}

impl Shl for ILVal {
    type Output = Self;

    fn shl(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Byte(l), Self::Byte(r)) => Self::Byte(l.overflowing_shl(r as u32).0),
            (Self::Short(l), Self::Short(r)) => Self::Short(l.overflowing_shl(r as u32).0),
            (Self::Word(l), Self::Word(r)) => Self::Word(l.overflowing_shl(r as u32).0),
            (Self::Quad(l), Self::Quad(r)) => Self::Quad(l.overflowing_shl(r as u32).0),
            _ => panic!("Incompatible sizes for remainder operation"),
        }
    }
}

impl Shr for ILVal {
    type Output = Self;

    fn shr(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Byte(l), Self::Byte(r)) => Self::Byte(l >> r),
            (Self::Short(l), Self::Short(r)) => Self::Short(l >> r),
            (Self::Word(l), Self::Word(r)) => Self::Word(l >> r),
            (Self::Quad(l), Self::Quad(r)) => Self::Quad(l >> r),
            _ => panic!("Incompatible sizes for remainder operation"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Emil<R: Reg, E: Endian> {
    /// No operation instruction.
    Nop,
    /// No return.
    NoRet,
    /// Perform a system call to the operating system.
    Syscall,
    /// Indicate that a breakpoint was hit.
    Bp,
    /// An undefined instruction was executed.
    Undef,
    /// Perform some kind of trap.
    Trap(u64),
    /// Set the value of an architectural register from an IL register.
    SetReg { reg: R, ilr: ILRef },
    /// Load an architectural register into an IL register.
    LoadReg { reg: R, ilr: ILRef },
    /// Set a temporary register.
    SetTemp { t: u8, ilr: ILRef },
    /// Load a temporary register into an IL register.
    LoadTemp { ilr: ILRef, t: u8 },
    /// Set the flag register or context bits to specific value.
    SetFlag(ILRef),
    /// Read the flag register or context bits into an IL register.
    Flag(ILRef),
    /// Store a value to memory
    Store { value: ILRef, addr: ILRef },
    /// Load a value from memory into an ILVal
    Load { size: u8, addr: ILRef, dest: ILRef },
    /// Push a value onto the stack
    Push(ILRef),
    /// Pop a value off of the stack
    Pop { dest: ILRef, size: u8 },
    /// Jump to a specific address in the binary.
    Jump(ILRef),
    /// Goto an LLIL index in the function.
    Goto(usize),
    /// Call a function with potential stack fixup.
    Call { target: ILRef, stack: u64 },
    /// Perform a tail call with some potential stack fixup.
    TailCall { target: ILRef, stack: u64 },
    /// Return from a function to an address.
    Ret(ILRef),
    /// Perform a conditional branch based on the condition to a specific address.
    If {
        /// Condition to check. If not-zero, go to tru_target, otherwise go to false_target
        condition: ILRef,
        true_target: usize,
        false_target: usize,
    },
    /// Perform an intrinsic operation.
    Intrinsic(u32),
    /// Load a constant into an IL register.
    Constant { reg: ILRef, value: u64, size: u8 },
    /// Add two values together.
    Add {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Bitwise and of two values.
    And {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Integer subtraction of two values.
    Sub {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Bitwise or of two values.
    Or {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Bitwise xor of two values.
    Xor {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Negate an integer value. Uses 2's-complement.
    Negate(ILRef, ILRef),
    /// Logical negation of an integer value. Just flips all bits.
    Not(ILRef, ILRef),
    /// Take the lowest n bytes of an expression.
    Truncate(ILRef, ILRef, u8),
    /// Logical shift right.
    Lsr {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Arithmetic shift right.
    Asr {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Logical shift left.
    Lsl {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Unsigned division of two values.
    Divu {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Signed division of two values.
    Divs {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Multiplication of two values.
    Mul {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Unsigned modulus of two values.
    Modu {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Signed modulus of two values.
    Mods {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Floating point addition of two values.
    Fadd {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Floating point subtraction of two values.
    Fsub {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Floating point multiplication of two values.
    Fmul {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Compare equal.
    CmpE {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Compare not equal.
    CmpNe {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Compare signed less than.
    CmpSlt {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Compare unsigned less than.
    CmpUlt {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Compare signed less than equal.
    CmpSle {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Compare unsigned less than equal.
    CmpUle {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Compare signed greater than equal.
    CmpSge {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Compare unsigned greater than equal.
    CmpUge {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Compare signed greater than.
    CmpSgt {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Compare unsigned greater than.
    CmpUgt {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Compare equal floating point.
    FcmpE {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Floating point compare not equal.
    FcmpNE {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Floating point compare less than.
    FcmpLT {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Floating point compare less than equal.
    FcmpLE {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Floating point compare greather than equal.
    FcmpGE {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Floating point compare greather than.
    FcmpGT {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    FcmpO {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    FcmpUO {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Floating point negation of a value.
    Fneg(ILRef, ILRef),
    /// Floating point absolute value.
    Fabs(ILRef, ILRef),
    /// Convert a boolean to an integer.
    BoolToInt(ILRef, ILRef, u8),
    /// Convert a floating point value to an integer
    FloatToInt(ILRef, ILRef, u8),
    /// Convert an integer to a floating point value.
    IntToFloat(ILRef, ILRef, u8),
    /// Value of an external pointer.
    ExternPtr(ILRef, u64),
    /// Sign extend a value.
    SignExtend(ILRef, ILRef, u8),
    /// Zero extend a value.
    ZeroExtend(ILRef, ILRef, u8),
    // The hook is not a Box<dyn FnMut(...)> because the project currently
    // relies on these instructions being copyable.
    /// Pseudo instruction to hook execution at a certain point in a program.
    ///
    /// This does not correspond to any specific instruction in LLIL. It is
    /// used to hook execution in a program so a user can run arbitrary code
    /// on the current state.
    #[cfg_attr(feature = "serde", serde(skip))]
    Hook(
        fn(&mut dyn State<Reg = R, Endianness = E>) -> HookStatus,
        usize,
    ),
    /// Breakpoint added by a user.
    ///
    /// This is a breakpoint that was not already present in the original
    /// program. This has extra information added to it so that emulation
    /// can stop at the breakpoint and then later continue through it.
    #[cfg_attr(feature = "serde", serde(skip))]
    UserBp(usize),
}
