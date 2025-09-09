use std::cmp::Ordering;
use std::fmt::Debug;
use std::ops::*;

use crate::arch::{State, SyscallResult};
use crate::emil::{Emil, ILRef, ILVal};
use crate::prog::Program;

use softmew::fault::Fault;

/// Reason that the emulator stopped executing.
#[derive(Clone, Debug)]
pub enum Exit {
    /// Program hit some instruction or syscall intended to stop execution.
    Exited,
    /// A breakpoint instruction was executed.
    ///
    /// This is a breakpoint that was present in the original program. Not a breakpoint that was
    /// added after the fact. When this is returned, the current instruction must be skipped over
    /// or the program counter needs to be updated in some other way to continue execution.
    Breakpoint,
    /// A breakpoint added after the fact was executed.
    ///
    /// This is a breakpoint that was added after the fact and was not present in the original
    /// program. Calling [`Emulator::proceed`] after this is returned will continue execution by
    /// skipping over the breakpoint. Just calling run or single step again will cause this
    /// breakpoint to be executed again.
    UserBreakpoint,
    /// Program executed a single instruction.
    SingleStep,
    /// A no-return instruction from LLIL was executed.
    NoReturn,
    /// An undefined instruction was executed.
    Undefined,
    /// Emulator took a single step in single step mode.
    Step,
    /// Program attempted to jump to or execute an invalid address.
    InstructionFault(u64),
    /// Program accessed memory that did not have the correct permissions.
    Access(Fault),
}

impl From<Fault> for Exit {
    fn from(value: Fault) -> Self {
        Self::Access(value)
    }
}

pub trait Endian: Debug + Clone + Copy {
    fn read(data: &[u8]) -> ILVal;
    fn write(value: ILVal, data: &mut [u8; 8]) -> usize;
}

#[derive(Debug, Clone, Copy)]
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
            _ => unreachable!("Invalid length"),
        }
    }

    fn write(value: ILVal, data: &mut [u8; 8]) -> usize {
        match value {
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
                data.copy_from_slice(&q.to_le_bytes());
                8
            }
        }
    }
}

pub struct Big;
// impl Endian for Big {}

/// Handle to a hook that was installed.
pub struct HookID(usize);

/// Handle to a breakpoint that was installed.
pub struct BpID(usize);

enum ExecutionState {
    Exit(Exit),
    Hook(usize),
    Continue,
}

impl From<Exit> for ExecutionState {
    fn from(e: Exit) -> Self {
        Self::Exit(e)
    }
}

/// Emulator for a specific BIL graph, state, and architecture.
pub struct Emulator<S: State> {
    /// Instructions to run.
    prog: Program<S::Reg, S::Endianness>,
    /// State of the device, mainly just memory.
    state: S,
    /// Intermediate language registers.
    ilrs: [ILVal; 255],
    /// Address of current instruction.
    pc: usize,
    /// List of instructions that have been hooked and what index they came from.
    replaced: Vec<(Emil<S::Reg, S::Endianness>, usize)>,
}

macro_rules! bin_op {
    ($state:ident, $o:ident, $l:ident, $r:ident, $op:path) => {{
        let left = $state.get_ilr($l);
        let right = $state.get_ilr($r);
        let out = $state.get_ilr_mut($o);
        *out = $op(left, right);
    }};
}

impl<S: State> Emulator<S> {
    pub fn new(prog: Program<S::Reg, S::Endianness>, state: S) -> Self {
        Self {
            prog,
            state,
            ilrs: [ILVal::Byte(0); 255],
            pc: 0,
            replaced: Vec::new(),
        }
    }

    pub fn add_hook(
        &mut self,
        addr: u64,
        hook: fn(&mut dyn State<Reg = S::Reg, Endianness = S::Endianness>),
    ) -> Option<HookID> {
        let replaced_idx = self.replaced.len();
        let mut hook = Emil::Hook(hook, replaced_idx);
        let idx = match self.prog.insn_map.get(&addr) {
            Some(i) => *i,
            None => return None,
        };
        let instr = self
            .prog
            .il
            .get_mut(idx)
            .expect("Invalid address mapping in program");
        std::mem::swap(&mut hook, instr);
        self.replaced.push((hook, idx));
        Some(HookID(replaced_idx))
    }

    pub fn remove_hook(&mut self, hook_id: HookID) {
        let mut hook = self.replaced[hook_id.0];
        std::mem::swap(&mut hook.0, self.prog.il.get_mut(hook.1).unwrap());
    }

    pub fn add_breakpoint(&mut self, addr: u64) -> Option<BpID> {
        let replaced_idx = self.replaced.len();
        let mut bp = Emil::UserBp(replaced_idx);
        let idx = match self.prog.insn_map.get(&addr) {
            Some(i) => *i,
            None => return None,
        };
        let inst = self.prog.il.get_mut(idx).expect("Invalid address mapping in program");
        std::mem::swap(&mut bp, inst);
        self.replaced.push((bp, idx));
        Some(BpID(replaced_idx))
    }

    pub fn get_state(&self) -> &S {
        &self.state
    }

    pub fn get_state_mut(&mut self) -> &mut S {
        &mut self.state
    }

    /// Get current program counter value.
    ///
    /// This will be a program address.
    pub fn curr_pc(&self) -> u64 {
        self.idx_to_addr(self.pc)
    }

    pub fn run(&mut self, addr: u64) -> Exit {
        match self.prog.insn_map.get(&addr) {
            Some(idx) => self.pc = *idx,
            None => return Exit::InstructionFault(addr),
        };
        loop {
            match self.emulate(*self.curr_inst()) {
                ExecutionState::Exit(e) => return e,
                ExecutionState::Continue => {},
                ExecutionState::Hook(idx) => {
                    let replaced = self.replaced[idx];
                    match self.emulate(replaced.0) {
                        ExecutionState::Exit(e) => return e,
                        ExecutionState::Continue => {},
                        ExecutionState::Hook(_) => unreachable!("Can't hook a hook instruction"),
                    }
                }
            }
        }
    }

    /// Continue execution at the current point in the program.
    ///
    /// This is equivalent to a continue operation. "continue" is a keyword in
    /// rust so it can't be the name of a method. Instead, this is just called
    /// proceed.
    pub fn proceed(&mut self) -> Exit {
        // Check if current execution is at a user breakpoint. If it is, get the instruction that
        // replaced it, execute it, then continue to normal execution.
        if let Emil::UserBp(idx) = self.curr_inst() {
            let replaced = self.replaced[*idx];
            match self.emulate(replaced.0) {
                ExecutionState::Exit(e) => return e,
                ExecutionState::Continue => {},
                ExecutionState::Hook(idx) => {
                    let replaced = self.replaced[idx];
                    match self.emulate(replaced.0) {
                        ExecutionState::Exit(e) => return e,
                        ExecutionState::Continue => {},
                        ExecutionState::Hook(_) => unreachable!("Can't hook a hook instruction"),
                    }
                }
            }
        }
        loop {
            match self.emulate(*self.curr_inst()) {
                ExecutionState::Exit(e) => return e,
                ExecutionState::Continue => {},
                ExecutionState::Hook(idx) => {
                    let replaced = self.replaced[idx];
                    match self.emulate(replaced.0) {
                        ExecutionState::Exit(e) => return e,
                        ExecutionState::Continue => {},
                        ExecutionState::Hook(_) => unreachable!("Can't hook a hook instruction"),
                    }
                }
            }
        }
    }

    /// Run a single instruction in the program then stop.
    ///
    /// Emulates a single target instruction and then returns. Upon success,
    /// [`Exit::SingleStep`] will be returned. Otherwise, one of the other exit
    /// codes will be returned.
    pub fn step(&mut self) -> Exit {
        let addr = self.curr_pc();
        while addr == self.curr_pc() {
            match self.emulate(*self.curr_inst()) {
                ExecutionState::Exit(e) => return e,
                ExecutionState::Continue => {},
                ExecutionState::Hook(idx) => {
                    let replaced = self.replaced[idx];
                    match self.emulate(replaced.0) {
                        ExecutionState::Exit(e) => return e,
                        ExecutionState::Continue => {},
                        ExecutionState::Hook(_) => unreachable!("Can't hook a hook instruction"),
                    }
                }
            }
        }
        Exit::SingleStep
    }

    #[inline(always)]
    fn curr_inst(&self) -> &Emil<S::Reg, S::Endianness> {
        unsafe { self.prog.il.get_unchecked(self.pc) }
    }

    fn emulate(&mut self, inst: Emil<S::Reg, S::Endianness>) -> ExecutionState {
        match inst {
            Emil::Nop => {}
            Emil::NoRet => return Exit::NoReturn.into(),
            Emil::Syscall => match self.state.syscall() {
                SyscallResult::Exit => return Exit::Exited.into(),
                SyscallResult::Error(e) => return ExecutionState::Exit(e.into()),
                _ => {}
            },
            Emil::Bp => return Exit::Breakpoint.into(),
            Emil::Undef => return Exit::Undefined.into(),
            Emil::Trap(v) => unimplemented!("Hit trap: {v}"),
            Emil::Intrinsic(intrinsic) => {
                self.state.intrinsic(intrinsic).unwrap();
            }
            Emil::Constant { reg, value, size } => {
                let val = ILVal::from(value);
                if size != 8 {
                    *self.get_ilr_mut(reg) = val.truncate(size);
                } else {
                    *self.get_ilr_mut(reg) = val;
                }
            }
            Emil::SetReg { reg, ilr } => {
                let val = self.get_ilr(ilr);
                self.state.write_reg(reg, val);
            }
            Emil::LoadReg { reg, ilr } => {
                let val = self.state.read_reg(reg);
                *self.get_ilr_mut(ilr) = val;
            }
            Emil::SetFlag(ilr) => {
                let val = self.get_ilr(ilr);
                self.state.set_flags(val);
            }
            Emil::Store { value, addr } => {
                let mut buf = [0u8; 8];
                let size = S::Endianness::write(self.get_ilr(value), &mut buf);
                let addr = self.get_ilr_mut(addr).extend_64();
                let write = self.state.write_mem(addr, &buf[0..size]);
                if let Err(f) = write {
                    return ExecutionState::Exit(f.into());
                }
            }
            Emil::Load { size, addr, dest } => {
                // prog.rs ensures that the load size will be 8 or less
                let mut buf = [0u8; 8];
                let addr = self.get_ilr(addr).extend_64();
                let read = self.state.read_mem(addr, &mut buf[0..size as usize]);
                if let Err(f) = read {
                    return ExecutionState::Exit(f.into());
                }
                let val = S::Endianness::read(&buf[0..size as usize]);
                *self.get_ilr_mut(dest) = val;
            }
            Emil::Jump(a) => {
                let addr = self.get_ilr(a).extend_64();
                if let Some(a) = self.prog.insn_map.get(&addr) {
                    self.pc = *a;
                } else {
                    return Exit::InstructionFault(addr).into();
                }
                return ExecutionState::Continue;
            }
            Emil::Goto(idx) => {
                self.pc = idx;
                return ExecutionState::Continue;
            }
            Emil::Call { target, stack: _ } => {
                let ret = self.pc + 1;
                if let Err(fault) = self.state.save_ret_addr(ret as u64) {
                    return ExecutionState::Exit(fault.into());
                }
                let target = self.get_ilr(target).extend_64();
                if let Some(dest_addr) = self.prog.insn_map.get(&target) {
                    self.pc = *dest_addr;
                } else {
                    return Exit::InstructionFault(target).into();
                }
                return ExecutionState::Continue;
            }
            Emil::TailCall { target, stack: _ } => {
                let target = self.get_ilr(target).extend_64();
                if let Some(dest_addr) = self.prog.insn_map.get(&target) {
                    self.pc = *dest_addr;
                } else {
                    return Exit::InstructionFault(target).into();
                }
                return ExecutionState::Continue;
            }
            Emil::Ret(ilr) => {
                // JIL indexes are saved so this should always be valid
                // TODO: Should be saving actual addresses.
                self.pc = self.get_ilr(ilr).extend_64() as usize;
                return ExecutionState::Continue;
            }
            Emil::If {
                condition,
                true_target,
                false_target,
            } => {
                let cond = self.get_ilr(condition).extend_64();
                if cond == 0 {
                    self.pc = false_target;
                } else {
                    self.pc = true_target;
                }
                return ExecutionState::Continue;
            }
            Emil::Add { out, left, right } => bin_op!(self, out, left, right, ILVal::add),
            Emil::And { out, left, right } => bin_op!(self, out, left, right, ILVal::bitand),
            Emil::Divu { out, left, right } => bin_op!(self, out, left, right, ILVal::div),
            Emil::Divs { out, left, right } => {
                bin_op!(self, out, left, right, ILVal::signed_div)
            }
            Emil::Mul { out, left, right } => bin_op!(self, out, left, right, ILVal::mul),
            Emil::Sub { out, left, right } => bin_op!(self, out, left, right, ILVal::sub),
            Emil::Or { out, left, right } => bin_op!(self, out, left, right, ILVal::bitor),
            Emil::Xor { out, left, right } => bin_op!(self, out, left, right, ILVal::bitxor),
            Emil::Lsl { out, left, right } => bin_op!(self, out, left, right, ILVal::shl),
            Emil::Lsr { out, left, right } => bin_op!(self, out, left, right, ILVal::shr),
            Emil::CmpE { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                *out = ILVal::Byte((left == right) as u8);
            }
            Emil::CmpNe { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                *out = ILVal::Byte((left != right) as u8);
            }
            Emil::CmpSlt { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                *out = ILVal::Byte((left.signed_cmp(&right) == Ordering::Less) as u8);
            }
            Emil::CmpUlt { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                *out = ILVal::Byte((left < right) as u8);
            }
            Emil::CmpSle { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                let ord = left.signed_cmp(&right);
                *out = ILVal::Byte((ord <= Ordering::Equal) as u8);
            }
            Emil::CmpUle { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                *out = ILVal::Byte((left <= right) as u8);
            }
            Emil::CmpSgt { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                *out = ILVal::Byte((left.signed_cmp(&right) == Ordering::Greater) as u8);
            }
            Emil::CmpUgt { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                *out = ILVal::Byte((left > right) as u8);
            }
            Emil::CmpSge { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                let ord = left.signed_cmp(&right);
                *out = ILVal::Byte((ord >= Ordering::Equal) as u8);
            }
            Emil::CmpUge { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                *out = ILVal::Byte((left >= right) as u8);
            }
            Emil::BoolToInt(out, val, size) => {
                let val = self.get_ilr(val).extend_64();
                let mut int = ILVal::Byte((val != 0) as u8);
                if size != 1 {
                    int = int.zext(size);
                }
                *self.get_ilr_mut(out) = int;
            }
            Emil::Truncate(out, val, size) => {
                *self.get_ilr_mut(out) = self.get_ilr(val).truncate(size);
            }
            Emil::SignExtend(out, val, size) => {
                *self.get_ilr_mut(out) = self.get_ilr(val).sext(size);
            }
            Emil::ZeroExtend(out, val, size) => {
                *self.get_ilr_mut(out) = self.get_ilr(val).zext(size);
            }
            Emil::Hook(func, idx) => {
                func(&mut self.state);
                return ExecutionState::Hook(idx);
            }
            instruction => {
                unimplemented!("Need to implement {instruction:?}");
            }
        }
        self.pc += 1;
        ExecutionState::Continue
    }

    #[inline(always)]
    fn idx_to_addr(&self, idx: usize) -> u64 {
        unsafe { *self.prog.addr_map.get_unchecked(idx) }
    }

    #[inline(always)]
    fn get_ilr(&self, idx: ILRef) -> ILVal {
        // SAFETY: The index is a u8. That has a valid range of 0-255. This is
        // indexing into an array of size 256 so it is not possible to index
        // past the end of the array or before the array.
        unsafe { *self.ilrs.get_unchecked(idx.0 as usize) }
    }

    #[inline(always)]
    fn get_ilr_mut(&mut self, idx: ILRef) -> &mut ILVal {
        // SAFETY: The index is a u8. That has a valid range of 0-255. This is
        // indexing into an array of size 256 so it is not possible to index
        // past the end of the array or before the array.
        unsafe { self.ilrs.get_unchecked_mut(idx.0 as usize) }
    }
}

fn sign_extend(val: u64, size: usize) -> u64 {
    debug_assert!(size <= 8);
    const MAX_SIZE: usize = 8;
    let shift_left = MAX_SIZE - size;
    let shifted_val = (val << shift_left) as i64;
    (shifted_val >> shift_left) as u64
}

const MASKS: [u64; 9] = [
    0x0,
    0xff,
    0xffff,
    0xffffff,
    0xffffffff,
    0xffffffffff,
    0xffffffffffff,
    0xffffffffffffff,
    0xffffffffffffffff,
];

fn zero_extend(val: u64, size: usize) -> u64 {
    debug_assert!(size <= 8);
    val & MASKS[size]
}
