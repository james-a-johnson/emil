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

use crate::arch::{Endian, Intrinsic, RegState, State};
use crate::emulate::HookStatus;
use crate::val::ILRef;
use std::fmt::Debug;

use softmew::page::Page;

/// Reference to an [`ILVal`].
pub enum Emil<P: Page, Regs: RegState, E: Endian, I: Intrinsic> {
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
    SetReg { reg: Regs::RegID, ilr: ILRef },
    /// Load an architectural register into an IL register.
    LoadReg { reg: Regs::RegID, ilr: ILRef },
    /// Set a temporary register.
    SetTemp { t: u8, ilr: ILRef },
    /// Load a temporary register into an IL register.
    LoadTemp { ilr: ILRef, t: u8 },
    /// Set the flag register or context bits to specific value.
    SetFlag(ILRef, u32),
    /// Read the flag register or context bits into an IL register.
    Flag(ILRef, u32),
    /// Store a value to memory
    Store { value: ILRef, addr: ILRef, size: u8 },
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
    Intrinsic(I),
    /// Load a constant into an IL register.
    Constant { reg: ILRef, value: u64, size: u8 },
    /// Add two values together.
    Add {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Check if an add would overflow or not.
    AddOf {
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
    /// Rotate right.
    Ror {
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
    /// Multiplication with extension to 64 bits unsigned.
    MuluDp {
        out: ILRef,
        left: ILRef,
        right: ILRef,
    },
    /// Multiplication with extension to 64 bits signed.
    MulsDp {
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
    Hook(
        fn(&mut dyn State<P, Registers = Regs, Endianness = E, Intrin = I>) -> HookStatus,
        usize,
    ),
    /// Breakpoint added by a user.
    ///
    /// This is a breakpoint that was not already present in the original
    /// program. This has extra information added to it so that emulation
    /// can stop at the breakpoint and then later continue through it.
    UserBp(usize),
}

impl<P: Page, Regs: RegState, E: Endian, I: Intrinsic> Clone for Emil<P, Regs, E, I> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<P: Page, Regs: RegState, E: Endian, I: Intrinsic> Copy for Emil<P, Regs, E, I> {}

impl<P: Page, Regs: RegState, E: Endian, I: Intrinsic> Debug for Emil<P, Regs, E, I> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nop => write!(f, "nop"),
            Self::NoRet => write!(f, "no return"),
            Self::Syscall => write!(f, "system call"),
            Self::Bp => write!(f, "breakpoint"),
            Self::Undef => write!(f, "undefined"),
            Self::Trap(t) => write!(f, "trap {t:#x}"),
            Self::SetReg { reg, ilr } => write!(f, "{reg:?} = {ilr:?}"),
            Self::LoadReg { reg, ilr } => write!(f, "{ilr:?} = {reg:?}"),
            Self::SetTemp { t, ilr } => write!(f, "temp({t}) = {ilr:?}"),
            Self::LoadTemp { ilr, t } => write!(f, "{ilr:?} = temp({t})"),
            Self::SetFlag(ilr, flag) => write!(f, "flag({flag}) = {ilr:?}"),
            Self::Flag(ilr, flag) => write!(f, "{ilr:?} = flag({flag})"),
            Self::Store { value, addr, size } => write!(f, "[{addr:?}]:{size} = {value:?}"),
            Self::Load { size, addr, dest } => write!(f, "{dest:?} = [{addr:?}]:{size}"),
            Self::Push(v) => write!(f, "push {v:?}"),
            Self::Pop { dest, size } => write!(f, "{dest:?} = pop:{size}"),
            Self::Jump(addr) => write!(f, "jump {addr:?}"),
            Self::Goto(idx) => write!(f, "goto {idx}"),
            Self::Call { target, .. } => write!(f, "call {target:?}"),
            Self::TailCall { target, .. } => write!(f, "tailcall {target:?}"),
            Self::Ret(dest) => write!(f, "return {dest:?}"),
            Self::If {
                condition,
                true_target,
                false_target,
            } => write!(f, "if ({condition:?}) {true_target} else {false_target}"),
            Self::Intrinsic(_) => write!(f, "intrinsic"),
            Self::Constant { reg, value, size } => write!(f, "{reg:?} = {value}:{size}"),
            Self::Add { out, left, right } => write!(f, "{out:?} = {left:?} + {right:?}"),
            Self::AddOf { out, left, right } => {
                write!(f, "{out:?} = overflow({left:?} + {right:?})")
            }
            Self::And { out, left, right } => write!(f, "{out:?} = {left:?} & {right:?}"),
            Self::Sub { out, left, right } => write!(f, "{out:?} = {left:?} - {right:?}"),
            Self::Or { out, left, right } => write!(f, "{out:?} = {left:?} | {right:?}"),
            Self::Xor { out, left, right } => write!(f, "{out:?} = {left:?} ^ {right:?}"),
            Self::Negate(out, src) => write!(f, "{out:?} = -{src:?}"),
            Self::Not(out, src) => write!(f, "{out:?} = !{src:?}"),
            Self::Truncate(out, src, size) => write!(f, "{out:?} = trunc({src:?}, {size})"),
            Self::Lsr { out, left, right } => write!(f, "{out:?} = {left:?} >> {right:?}"),
            Self::Asr { out, left, right } => write!(f, "{out:?} = {left:?} >>> {right:?}"),
            Self::Lsl { out, left, right } => write!(f, "{out:?} = {left:?} << {right:?}"),
            Self::Ror { out, left, right } => write!(f, "{out:?} = {left:?} ror {right:?}"),
            Self::Divu { out, left, right } => write!(f, "{out:?} = {left:?} u/ {right:?}"),
            Self::Divs { out, left, right } => write!(f, "{out:?} = {left:?} s/ {right:?}"),
            Self::Mul { out, left, right } => write!(f, "{out:?} = {left:?} * {right:?}"),
            Self::MuluDp { out, left, right } => write!(f, "{out:?} = {left:?} u2* {right:?}"),
            Self::MulsDp { out, left, right } => write!(f, "{out:?} = {left:?} s2* {right:?}"),
            Self::Modu { out, left, right } => write!(f, "{out:?} = {left:?} u% {right:?}"),
            Self::Mods { out, left, right } => write!(f, "{out:?} = {left:?} s% {right:?}"),
            Self::Fadd { out, left, right } => write!(f, "{out:?} = {left:?} f+ {right:?}"),
            Self::Fsub { out, left, right } => write!(f, "{out:?} = {left:?} f- {right:?}"),
            Self::Fmul { out, left, right } => write!(f, "{out:?} = {left:?} f* {right:?}"),
            Self::CmpE { out, left, right } => write!(f, "{out:?} = {left:?} == {right:?}"),
            Self::CmpNe { out, left, right } => write!(f, "{out:?} = {left:?} != {right:?}"),
            Self::CmpSlt { out, left, right } => write!(f, "{out:?} = {left:?} s< {right:?}"),
            Self::CmpUlt { out, left, right } => write!(f, "{out:?} = {left:?} u< {right:?}"),
            Self::CmpSle { out, left, right } => write!(f, "{out:?} = {left:?} s<= {right:?}"),
            Self::CmpUle { out, left, right } => write!(f, "{out:?} = {left:?} u<= {right:?}"),
            Self::CmpSge { out, left, right } => write!(f, "{out:?} = {left:?} s>= {right:?}"),
            Self::CmpUge { out, left, right } => write!(f, "{out:?} = {left:?} u>= {right:?}"),
            Self::CmpSgt { out, left, right } => write!(f, "{out:?} = {left:?} s> {right:?}"),
            Self::CmpUgt { out, left, right } => write!(f, "{out:?} = {left:?} u> {right:?}"),
            Self::FcmpE { out, left, right } => write!(f, "{out:?} = {left:?} f== {right:?}"),
            Self::FcmpNE { out, left, right } => write!(f, "{out:?} = {left:?} f!= {right:?}"),
            Self::FcmpLT { out, left, right } => write!(f, "{out:?} = {left:?} f< {right:?}"),
            Self::FcmpLE { out, left, right } => write!(f, "{out:?} = {left:?} f<= {right:?}"),
            Self::FcmpGE { out, left, right } => write!(f, "{out:?} = {left:?} f>= {right:?}"),
            Self::FcmpGT { out, left, right } => write!(f, "{out:?} = {left:?} f> {right:?}"),
            Self::FcmpO { out, left, right } => write!(f, "{out:?} = {left:?} fo {right:?}"),
            Self::FcmpUO { out, left, right } => write!(f, "{out:?} = {left:?} fuo {right:?}"),
            Self::Fneg(out, src) => write!(f, "{out:?} = f-{src:?}"),
            Self::Fabs(out, src) => write!(f, "{out:?} = |{src:?}|"),
            Self::BoolToInt(out, src, size) => write!(f, "{out:?}:{size} = b2i({src:?})"),
            Self::FloatToInt(out, src, size) => write!(f, "{out:?}:{size} = f2i({src:?})"),
            Self::IntToFloat(out, src, size) => write!(f, "{out:?}:{size} = i2f({src:?})"),
            Self::ExternPtr(out, val) => write!(f, "{out:?} = extern({val:#x})"),
            Self::SignExtend(out, src, size) => write!(f, "{out:?}:{size} = sx({src:?})"),
            Self::ZeroExtend(out, src, size) => write!(f, "{out:?}:{size} = zx({src:?})"),
            Self::Hook(h, idx) => write!(f, "hook({h:?}, {idx})"),
            Self::UserBp(bp) => write!(f, "bp({bp})"),
        }
    }
}
