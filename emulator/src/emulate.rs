use crate::arch::{Endian, RegState, State, SyscallResult};
use crate::emil::{Emil, ILRef, ILVal};
use crate::prog::Program;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::Debug;
use std::ops::*;

use softmew::fault::Fault;
use softmew::page::Page;

/// Number of temporary registers to use.
///
/// Currently the most I have seen used in a function is 17.
const NUM_TEMPS: usize = 32;

/// Function that can be used to hook specific instructions.
pub type HookFn<P, Regs, E, I> =
    fn(&mut dyn State<P, Registers = Regs, Endianness = E, Intrin = I>) -> HookStatus;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AccessType {
    Read,
    Write,
}

// TODO: Figure out a way to pass register values when hitting a watch-point.
/// Function that can be used to hook reads or writes of specific addresses.
///
/// # Parameters
/// - Address of the instruction that is doing the read or write
/// - Address of the first byte being read or written in the current access
/// - Data that is being written or the data that was read
pub type WatchFn = fn(u64, u64, AccessType, &mut [u8]);

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
    /// Hook function caused emulation to stop.
    ///
    /// This is returned when a hook returns [`HookStatus::Exit`].
    HookExit,
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

/// Handle to a hook that was installed.
pub struct HookID(usize);

/// Status that can be returned from a hook function.
///
/// These can affect program flow and will allow a hook to change how a program
/// will execute.
pub enum HookStatus {
    /// Continue program execution normally.
    Continue,
    /// Exit the program.
    Exit,
    /// Jump execution to a specific address.
    Goto(u64),
    /// Return that a fault occurred during hooking some instruction.
    Fault(Fault),
}

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
pub struct Emulator<P: Page, S: State<P>> {
    /// Instructions to run.
    prog: Program<P, S::Registers, S::Endianness, S::Intrin>,
    /// State of the device, mainly just memory.
    state: S,
    /// Intermediate language registers.
    ilrs: [ILVal; 255],
    /// Temporary registers used by LLIL.
    temps: [ILVal; NUM_TEMPS],
    /// Address of current instruction.
    pc: usize,
    /// List of instructions that have been hooked and what index they came from.
    replaced: Vec<(Emil<P, S::Registers, S::Endianness, S::Intrin>, usize)>,
    /// Addresses that
    watch: HashMap<u64, WatchFn>,
}

macro_rules! bin_op {
    ($state:ident, $o:ident, $l:ident, $r:ident, $op:path) => {{
        let left = $state.get_ilr($l);
        let right = $state.get_ilr($r);
        let out = $state.get_ilr_mut($o);
        *out = $op(left, right);
    }};
}

impl<P: Page, S: State<P>> Emulator<P, S> {
    /// Create a new emulator from the given program and state.
    ///
    /// `prog` is the actual program that is to be emulated. `state` will
    /// determine how the program interacts with its environment. It will
    /// emulate the memory accesses and system calls.
    pub fn new(prog: Program<P, S::Registers, S::Endianness, S::Intrin>, state: S) -> Self {
        Self {
            prog,
            state,
            ilrs: [ILVal::Byte(0); 255],
            temps: [ILVal::Byte(0); NUM_TEMPS],
            pc: 0,
            replaced: Vec::new(),
            watch: HashMap::new(),
        }
    }

    /// Hook a specific instruction in the program.
    ///
    /// A hook is some function that will run before an instruction is emulated.
    /// The hook will have mutable access to the current state of the program.
    /// The hook can just observe state using that or modify it in some way to
    /// change the state.
    ///
    /// The hook should return what action the emulator should take after
    /// running the hook. Those options are to exit, continue, or jump to a
    /// specific target address.
    ///
    /// # Return
    /// This returns a [`HookID`] that can be used to reference the hook upon
    /// success. Otherwise `None` will be returned. Installing the hook will
    /// only fail if an invalid address is passed.
    pub fn add_hook(
        &mut self,
        addr: u64,
        hook: HookFn<P, S::Registers, S::Endianness, S::Intrin>,
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

    /// Remove the hook from the program.
    pub fn remove_hook(&mut self, hook_id: HookID) {
        let mut hook = self.replaced[hook_id.0];
        std::mem::swap(&mut hook.0, self.prog.il.get_mut(hook.1).unwrap());
    }

    /// Place a breakpoint at a specific instruction in the program.
    ///
    /// This breakpoint will cause the emulator to exit with [`Exit::UserBreakpoint`].
    /// There may already have been breakpoints in the program in which case
    /// [`Exit::Breakpoint`] will be returned.
    ///
    /// # Return
    /// Returns an identifier for the placed breakpoint on success. That identifier
    /// can be used to refer to the specific breakpoint later. Otherwise, `None`
    /// is returned.
    pub fn add_breakpoint(&mut self, addr: u64) -> Option<BpID> {
        let replaced_idx = self.replaced.len();
        let mut bp = Emil::UserBp(replaced_idx);
        let idx = match self.prog.insn_map.get(&addr) {
            Some(i) => *i,
            None => return None,
        };
        let inst = self
            .prog
            .il
            .get_mut(idx)
            .expect("Invalid address mapping in program");
        std::mem::swap(&mut bp, inst);
        self.replaced.push((bp, idx));
        Some(BpID(replaced_idx))
    }

    /// Add a single address to the set of addresses to watch.
    pub fn add_watch_point(&mut self, addr: u64, hook: WatchFn) {
        self.watch.insert(addr, hook);
    }

    /// Add a range of addresses to the set of addresses to watch.
    pub fn add_watch_addrs(&mut self, addrs: Range<u64>, hook: WatchFn) {
        for addr in addrs {
            self.watch.insert(addr, hook);
        }
    }

    /// Remove the given breakpoint from the program.
    pub fn remove_breakpoint(&mut self, bp_id: BpID) {
        let mut bp = self.replaced[bp_id.0];
        std::mem::swap(&mut bp.0, self.prog.il.get_mut(bp.1).unwrap());
    }

    pub fn get_state(&self) -> &S {
        &self.state
    }

    pub fn get_state_mut(&mut self) -> &mut S {
        &mut self.state
    }

    /// Get a reference to the underlying program.
    pub fn get_prog(&self) -> &Program<P, S::Registers, S::Endianness, S::Intrin> {
        &self.prog
    }

    /// Get a mutable reference to the underlying program.
    pub fn get_prog_mut(&mut self) -> &mut Program<P, S::Registers, S::Endianness, S::Intrin> {
        &mut self.prog
    }

    /// Get current program counter value.
    ///
    /// This will be a program address.
    pub fn curr_pc(&self) -> u64 {
        self.idx_to_addr(self.pc)
    }

    /// Set the address to start emulation at.
    ///
    /// You can call this function and then you can can [`Emulator::proceed`]
    /// and it will start executing at the correct address.
    ///
    /// # Return
    /// Returns if the pc value was successfully updated. Updating the PC value can fail if an invalid address is
    /// provided.
    pub fn set_pc(&mut self, addr: u64) -> bool {
        let idx = self.prog.insn_map.get(&addr);
        if let Some(idx) = idx {
            self.pc = *idx;
            true
        } else {
            false
        }
    }

    pub fn run(&mut self, addr: u64) -> Exit {
        match self.prog.insn_map.get(&addr) {
            Some(idx) => self.pc = *idx,
            None => return Exit::InstructionFault(addr),
        };
        loop {
            match self.exec_one() {
                ExecutionState::Exit(e) => return e,
                ExecutionState::Continue => continue,
                ExecutionState::Hook(_) => unreachable!("Hook can't be returned from exec_one"),
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
                ExecutionState::Continue => {}
                ExecutionState::Hook(idx) => {
                    let replaced = self.replaced[idx];
                    match self.emulate(replaced.0) {
                        ExecutionState::Exit(e) => return e,
                        ExecutionState::Continue => {}
                        ExecutionState::Hook(_) => unreachable!("Can't hook a hook instruction"),
                    }
                }
            }
        }
        loop {
            match self.exec_one() {
                ExecutionState::Exit(e) => return e,
                ExecutionState::Continue => continue,
                ExecutionState::Hook(_) => unreachable!("Hook can't be returned from exec_one"),
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
            match self.exec_one() {
                ExecutionState::Exit(e) => return e,
                ExecutionState::Continue => continue,
                ExecutionState::Hook(_) => unreachable!("Hook can't be returned from exec_one"),
            }
        }
        Exit::SingleStep
    }

    #[inline(always)]
    fn exec_one(&mut self) -> ExecutionState {
        match self.emulate(*self.curr_inst()) {
            ExecutionState::Hook(idx) => {
                let replaced = self.replaced[idx];
                match self.emulate(replaced.0) {
                    ExecutionState::Hook(_) => unreachable!("Can't hook a hook instruction"),
                    e => return e,
                }
            }
            e => return e,
        }
    }

    /// Get the EMIL instruction at the current pc value.
    #[inline(always)]
    fn curr_inst(&self) -> &Emil<P, S::Registers, S::Endianness, S::Intrin> {
        // SAFETY: self.pc will always be set to a valid index in the il array.
        unsafe { self.prog.il.get_unchecked(self.pc) }
    }

    /// Emulate a single instruction.
    fn emulate(&mut self, inst: Emil<P, S::Registers, S::Endianness, S::Intrin>) -> ExecutionState {
        match inst {
            Emil::Nop => {}
            Emil::NoRet => return Exit::NoReturn.into(),
            Emil::Syscall => match self.state.syscall(self.curr_pc()) {
                SyscallResult::Exit => return Exit::Exited.into(),
                SyscallResult::Error(e) => return ExecutionState::Exit(e.into()),
                _ => {}
            },
            Emil::Bp => return Exit::Breakpoint.into(),
            Emil::Undef => return Exit::Undefined.into(),
            Emil::Trap(v) => unimplemented!("Hit trap: {v}"),
            Emil::Intrinsic(intrinsic) => {
                self.state.intrinsic(&intrinsic).unwrap();
            }
            Emil::Constant { reg, value, size } => {
                let val = ILVal::from(value);
                *self.get_ilr_mut(reg) = val.truncate(size);
            }
            Emil::SetReg { reg, ilr } => {
                let val = self.get_ilr(ilr);
                self.state.regs().write(reg, val);
            }
            Emil::LoadReg { reg, ilr } => {
                let val = self.state.regs().read(reg);
                *self.get_ilr_mut(ilr) = val;
            }
            Emil::SetTemp { t, ilr } => {
                self.temps[t as usize] = self.get_ilr(ilr);
            }
            Emil::LoadTemp { ilr, t } => {
                *self.get_ilr_mut(ilr) = self.temps[t as usize];
            }
            Emil::SetFlag(ilr, id) => {
                let val = self.get_ilr(ilr);
                self.state.set_flag(val.truth(), id);
            }
            Emil::Flag(ilr, id) => {
                let val = ILVal::Flag(self.state.get_flag(id));
                *self.get_ilr_mut(ilr) = val;
            }
            Emil::Store { value, addr, size } => {
                let value = self.get_ilr(value);
                let addr = self.get_ilr_mut(addr).extend_64() as usize;
                let pc = self.curr_pc();
                debug_assert_eq!(size as usize, value.size());
                let mem = self
                    .state
                    .mem()
                    .get_slice_mut(addr..addr + size as usize, softmew::Perm::WRITE);
                if let Err(f) = mem {
                    return ExecutionState::Exit(f.into());
                }
                let mem = mem.unwrap();
                S::Endianness::write(value, mem);
                let addr = addr as u64;
                if let Some(hook) = self.watch.get(&addr) {
                    hook(pc, addr, AccessType::Write, mem);
                }
            }
            Emil::Load { size, addr, dest } => {
                let pc = self.curr_pc();
                let addr = self.get_ilr(addr).extend_64() as usize;
                let data = self
                    .state
                    .mem()
                    .get_slice_mut(addr..addr + size as usize, softmew::Perm::READ);
                if let Err(f) = data {
                    return ExecutionState::Exit(f.into());
                }
                let data = data.unwrap();
                let addr = addr as u64;
                if let Some(hook) = self.watch.get(&addr) {
                    hook(pc, addr, AccessType::Read, data);
                }
                let val = S::Endianness::read(data);
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
                // Need to determine the return address for this call instruction. This is making
                // the assumption that a call instruction will return to the next valid address.
                // That is true for most architectures and I believe is true for all architectures
                // that binary ninja supports so this should be a fine assumption to make for now.
                // Find the next valid address by looking for the next address different from the
                // current one in the addr_map. It is not necessarily just the mapping of the next
                // IL address because binary ninja will sometimes add a goto to the correct next
                // address after a call instruction. So just blindly taking the address of the next
                // IL index might just create an infinite loop of returning to the call of the
                // function that needs to be returned from.
                // Apparently this is a bit more complicated. Looking at an Arm64 binary, there is a call
                // and a goto associated with the same address but different LLIL indices. That goto
                // does just jump to the next instruction but that is not the next address that would
                // show up when going through the LLIL indices. So need to increment by actual address
                // as opposed to going through an LLIL index based order.
                let ret_addr = if let Emil::Goto(ret_idx) = self.prog.il[self.pc + 1] {
                    // Need to return to this address instead.
                    self.prog.addr_map[ret_idx]
                } else {
                    let curr_addr = self.curr_pc();
                    self.prog.addr_map[self.pc..]
                        .iter()
                        .filter(|x| **x > curr_addr)
                        .map(|x| *x)
                        .nth(0)
                        .unwrap_or(curr_addr + 1)
                };
                if let Err(fault) = self.state.save_ret_addr(ret_addr) {
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
                let address = self.get_ilr(ilr).extend_64();
                return match self.prog.insn_map.get(&address) {
                    Some(idx) => {
                        self.pc = *idx;
                        ExecutionState::Continue
                    }
                    None => Exit::InstructionFault(address).into(),
                };
            }
            Emil::If {
                condition,
                true_target,
                false_target,
            } => {
                let cond = self.get_ilr(condition).truth();
                if cond {
                    self.pc = true_target;
                } else {
                    self.pc = false_target;
                }
                return ExecutionState::Continue;
            }
            Emil::Add { out, left, right } => bin_op!(self, out, left, right, ILVal::add),
            Emil::AddOf { out, left, right } => bin_op!(self, out, left, right, ILVal::add_of),
            Emil::And { out, left, right } => bin_op!(self, out, left, right, ILVal::bitand),
            Emil::Divu { out, left, right } => bin_op!(self, out, left, right, ILVal::div),
            Emil::Divs { out, left, right } => {
                bin_op!(self, out, left, right, ILVal::signed_div)
            }
            Emil::Mul { out, left, right } => bin_op!(self, out, left, right, ILVal::mul),
            Emil::MuluDp { out, left, right } => bin_op!(self, out, left, right, ILVal::mulu_dp),
            Emil::MulsDp { out, left, right } => bin_op!(self, out, left, right, ILVal::muls_dp),
            Emil::Not(dest, source) => *self.get_ilr_mut(dest) = !self.get_ilr(source),
            Emil::Negate(dest, source) => *self.get_ilr_mut(dest) = -self.get_ilr(source),
            Emil::Sub { out, left, right } => bin_op!(self, out, left, right, ILVal::sub),
            Emil::Or { out, left, right } => bin_op!(self, out, left, right, ILVal::bitor),
            Emil::Xor { out, left, right } => bin_op!(self, out, left, right, ILVal::bitxor),
            Emil::Lsl { out, left, right } => bin_op!(self, out, left, right, ILVal::shl),
            Emil::Lsr { out, left, right } => bin_op!(self, out, left, right, ILVal::shr),
            Emil::Asr { out, left, right } => bin_op!(self, out, left, right, ILVal::asr),
            Emil::Ror { out, left, right } => bin_op!(self, out, left, right, ILVal::rotate_right),
            Emil::CmpE { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                *out = ILVal::Flag(left == right);
            }
            Emil::CmpNe { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                *out = ILVal::Flag(left != right);
            }
            Emil::CmpSlt { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                *out = ILVal::Flag(left.signed_cmp(&right) == Ordering::Less);
            }
            Emil::CmpUlt { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                *out = ILVal::Flag(left < right);
            }
            Emil::CmpSle { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                let ord = left.signed_cmp(&right);
                *out = ILVal::Flag(ord <= Ordering::Equal);
            }
            Emil::CmpUle { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                *out = ILVal::Flag(left <= right);
            }
            Emil::CmpSgt { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                *out = ILVal::Flag(left.signed_cmp(&right) == Ordering::Greater);
            }
            Emil::CmpUgt { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                *out = ILVal::Flag(left > right);
            }
            Emil::CmpSge { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                let ord = left.signed_cmp(&right);
                *out = ILVal::Flag(ord >= Ordering::Equal);
            }
            Emil::CmpUge { out, left, right } => {
                let left = self.get_ilr(left);
                let right = self.get_ilr(right);
                let out = self.get_ilr_mut(out);
                *out = ILVal::Flag(left >= right);
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
                match func(&mut self.state) {
                    HookStatus::Continue => return ExecutionState::Hook(idx),
                    HookStatus::Exit => return ExecutionState::Exit(Exit::HookExit),
                    HookStatus::Fault(f) => return ExecutionState::Exit(f.into()),
                    HookStatus::Goto(addr) => {
                        let idx = self.prog.insn_map.get(&addr);
                        if let Some(idx) = idx {
                            self.pc = *idx;
                            return ExecutionState::Continue;
                        } else {
                            return ExecutionState::Exit(Exit::InstructionFault(addr));
                        }
                    }
                };
            }
            Emil::UserBp(_) => return ExecutionState::Exit(Exit::UserBreakpoint),
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
