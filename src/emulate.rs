use std::cmp::Ordering;
use std::collections::HashSet;
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
    Breakpoint,
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

pub trait Endian {
    fn read(data: &[u8]) -> ILVal;
    fn write(value: ILVal, data: &mut [u8; 8]) -> usize;
}

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
                data.copy_from_slice(&s.to_le_bytes());
                2
            }
            ILVal::Word(w) => {
                data.copy_from_slice(&w.to_le_bytes());
                4
            }
            ILVal::Quad(q) => {
                data.copy_from_slice(&q.to_le_bytes());
                4
            }
        }
    }
}

pub struct Big;
// impl Endian for Big {}

/// Emulator for a specific BIL graph, state, and architecture.
pub struct Emulator<S: State> {
    /// Instructions to run.
    prog: Program<S::Reg>,
    /// Breakpoints.
    bps: HashSet<u64>,
    /// State of the device, mainly just memory.
    state: S,
    /// Intermediate language registers.
    ilrs: [ILVal; 255],
    /// Address of current instruction.
    pc: usize,
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
    pub fn new(prog: Program<S::Reg>, state: S) -> Self {
        Self {
            prog,
            state,
            bps: HashSet::new(),
            ilrs: [ILVal::Byte(0); 255],
            pc: 0,
        }
    }

    pub fn add_bp(&mut self, addr: u64) {
        self.bps.insert(addr);
    }

    pub fn remove_bp(&mut self, addr: u64) {
        self.bps.remove(&addr);
    }

    pub fn get_state(&self) -> &S {
        &self.state
    }

    pub fn get_state_mut(&mut self) -> &mut S {
        &mut self.state
    }

    /// Get current program counter value.
    ///
    /// This will be an index into the instruction list and not match what you can find in binary
    /// ninja.
    pub fn curr_pc(&self) -> usize {
        self.pc
    }

    pub fn emulate(&mut self, addr: u64) -> Exit {
        match self.prog.insn_map.get(&addr) {
            Some(idx) => self.pc = *idx,
            None => return Exit::InstructionFault(addr),
        };
        'inst_loop: loop {
            let inst = unsafe { *self.prog.il.get_unchecked(self.pc) };
            match inst {
                Emil::Nop => {}
                Emil::NoRet => return Exit::NoReturn,
                Emil::Syscall => match self.state.syscall() {
                    SyscallResult::Exit => return Exit::Exited,
                    SyscallResult::Error(e) => return e.into(),
                    _ => {}
                },
                Emil::Bp => return Exit::Breakpoint,
                Emil::Undef => panic!("Executed undefined instruction"),
                Emil::Trap(v) => unimplemented!("Hit trap: {v}"),
                Emil::Intrinsic(intrinsic) => {
                    self.state.intrinsic(intrinsic).unwrap();
                }
                Emil::Constant { reg, value } => {
                    *self.get_ilr_mut(reg) = ILVal::from(value);
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
                        return f.into();
                    }
                }
                Emil::Load { size, addr, dest } => {
                    // prog.rs ensures that the load size will be 8 or less
                    let mut buf = [0u8; 8];
                    let addr = self.get_ilr(addr).extend_64();
                    let read = self.state.read_mem(addr, &mut buf[0..size as usize]);
                    if let Err(f) = read {
                        return f.into();
                    }
                    let val = S::Endianness::read(&buf[0..size as usize]);
                    *self.get_ilr_mut(dest) = val;
                }
                Emil::Jump(a) => {
                    let addr = self.get_ilr(a).extend_64();
                    if let Some(a) = self.prog.insn_map.get(&addr) {
                        self.pc = *a;
                    } else {
                        return Exit::InstructionFault(addr);
                    }
                    continue 'inst_loop;
                }
                Emil::Goto(idx) => {
                    self.pc = idx;
                    continue 'inst_loop;
                }
                Emil::Call { target, stack: _ } => {
                    let ret = self.pc + 1;
                    if let Err(fault) = self.state.save_ret_addr(ret as u64) {
                        return fault.into();
                    }
                    let target = self.get_ilr(target).extend_64();
                    if let Some(dest_addr) = self.prog.insn_map.get(&target) {
                        self.pc = *dest_addr;
                    } else {
                        return Exit::InstructionFault(target);
                    }
                    continue 'inst_loop;
                }
                Emil::TailCall { target, stack: _ } => {
                    let target = self.get_ilr(target).extend_64();
                    if let Some(dest_addr) = self.prog.insn_map.get(&target) {
                        self.pc = *dest_addr;
                    } else {
                        return Exit::InstructionFault(target);
                    }
                    continue 'inst_loop;
                }
                Emil::Ret(ilr) => {
                    // JIL indexes are saved so this should always be valid
                    self.pc = self.get_ilr(ilr).extend_64() as usize;
                    continue 'inst_loop;
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
                    continue 'inst_loop;
                }
                Emil::Add { out, left, right } => bin_op!(self, out, left, right, ILVal::add),
                Emil::And { out, left, right } => bin_op!(self, out, left, right, ILVal::bitand),
                Emil::Or { out, left, right } => bin_op!(self, out, left, right, ILVal::bitor),
                Emil::Lsl { out, left, right } => bin_op!(self, out, left, right, ILVal::shl),
                Emil::CmpE { out, left, right } => {
                    let left = self.get_ilr(left);
                    let right = self.get_ilr(right);
                    let out = self.get_ilr_mut(out);
                    *out = ILVal::Byte((left != right) as u8);
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
                Emil::Truncate(out, val, size) => {
                    *self.get_ilr_mut(out) = self.get_ilr(val).truncate(size);
                }
                instruction => {
                    unimplemented!("Need to implement {instruction:?}");
                }
            }
            self.pc += 1;
        }
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
