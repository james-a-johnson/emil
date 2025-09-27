use crate::arch::{FileDescriptor, Intrinsic, RegState, Register, State, SyscallResult};
use crate::emil::ILVal;
use crate::emulate::Little;
use crate::os::linux::LinuxSyscalls;
use binaryninja::architecture::Register as BNReg;
use binaryninja::low_level_il::expression::ExpressionHandler;
use binaryninja::low_level_il::expression::LowLevelILExpressionKind as ExprKind;
use binaryninja::low_level_il::operation::RegOrFlag;
use from_id::FromId;
use softmew::page::{Page, SimplePage};
use softmew::{MMU, Perm};

use std::collections::{HashMap, VecDeque};
use std::ops::{Index, IndexMut, Range};

#[derive(Clone, Copy, Debug)]
pub enum ArmIntrinsic {
    WriteMSR(Arm64Reg, u32),
    ReadMSR(Arm64Reg, u32),
    Dmb,
}

impl Intrinsic for ArmIntrinsic {
    fn parse(
        intrinsic: &binaryninja::low_level_il::operation::Operation<
            '_,
            binaryninja::low_level_il::function::Finalized,
            binaryninja::low_level_il::function::NonSSA,
            binaryninja::low_level_il::operation::Intrinsic,
        >,
    ) -> Result<Self, String> {
        let id = intrinsic.intrinsic().expect("Invalid intrinsic").id.0;
        match id {
            5 => Ok(ArmIntrinsic::Dmb),
            13 => {
                // Read msr into an architecture register.
                // First element of output array should be a register.
                let outputs = intrinsic.outputs();
                let reg = outputs
                    .get(0)
                    .ok_or(format!("MSR is not writing a register"))?;
                let reg = if let RegOrFlag::Reg(r) = reg {
                    Arm64Reg::try_from(r.id().0).unwrap()
                } else {
                    return Err(format!("Can't write msr to a flag"));
                };
                let msr = match intrinsic.inputs().kind() {
                    ExprKind::CallParamSsa(p) => {
                        if let Some(ExprKind::Const(c)) = p.param_exprs().get(0).map(|e| e.kind()) {
                            c.value() as u32
                        } else {
                            return Err(format!("Read MSR param not a constant"));
                        }
                    }
                    _ => return Err(format!("Inputs to read msr were not a parameter list")),
                };
                Ok(Self::ReadMSR(reg, msr))
            }
            14 => {
                // Write architecture register into system register.
                // All information is in the inputs array. That will have the system register number and then the
                // architecture register ID.
                let inputs = intrinsic.inputs().kind();
                let sys_id = match inputs {
                    ExprKind::CallParamSsa(ref p) => {
                        if let Some(ExprKind::Const(c)) = p.param_exprs().get(0).map(|e| e.kind()) {
                            c.value() as u32
                        } else {
                            return Err(format!("First param of write MSR is not a constant"));
                        }
                    }
                    _ => return Err(format!("Inputs to write MSR were not a parameter list")),
                };
                let reg = match inputs {
                    ExprKind::CallParamSsa(ref p) => {
                        if let Some(ExprKind::Reg(r)) = p.param_exprs().get(1).map(|e| e.kind()) {
                            r.source_reg().id().0
                        } else {
                            return Err(format!("Second param of write MSR is not a register"));
                        }
                    }
                    _ => return Err(format!("Inputs to write MSR were not a parameter list")),
                };
                let reg = Arm64Reg::try_from(reg)
                    .map_err(|e| format!("{e} is an invalid arm64 register id for write MSR"))?;
                Ok(Self::WriteMSR(reg, sys_id))
            }
            _ => Err(format!("Don't support {id} yet")),
        }
    }
}

pub struct LinuxArm64<S> {
    pub regs: Arm64State,
    pub mem: MMU<SimplePage>,
    pub flag: u64,
    pub conds: [u8; 32],
    pub syscalls: S,
    pub tpid: u64,
}

impl<S> LinuxArm64<S> {
    pub const ARCH_NAME: &'static str = "aarch64";

    pub fn new(syscalls: S) -> Self {
        let regs = Arm64State::default();
        let mmu = MMU::new();
        Self {
            regs,
            mem: mmu,
            flag: 0,
            conds: [0u8; 32],
            syscalls,
            tpid: 0,
        }
    }

    #[inline]
    pub fn memory(&self) -> &MMU<SimplePage> {
        &self.mem
    }

    #[inline]
    pub fn memory_mut(&mut self) -> &mut MMU<SimplePage> {
        &mut self.mem
    }

    #[inline]
    pub fn regs(&self) -> &Arm64State {
        &self.regs
    }

    #[inline]
    pub fn regs_mut(&mut self) -> &mut Arm64State {
        &mut self.regs
    }
}

macro_rules! syscalls {
    ($handler:ident, $sys_no:ident, $(($num:literal, $name:ident)),*) => {
        match $sys_no {
            $($num => $handler.syscalls.$name(&mut $handler.regs, &mut $handler.mem),)*
            no => unimplemented!("Syscall {no:#x} is not implemented"),
        }
    };
}

impl<S: LinuxSyscalls<Arm64State, MMU<SimplePage>>> State for LinuxArm64<S> {
    type Reg = Arm64Reg;
    type Endianness = Little;
    type Intrin = ArmIntrinsic;

    fn read_reg(&self, id: Self::Reg) -> ILVal {
        self.regs.get(id)
    }

    fn write_reg(&mut self, id: Self::Reg, value: ILVal) {
        match id {
            Arm64Reg::w0 => self.regs.gregs[0] = value.to_u32() as u64,
            Arm64Reg::w1 => self.regs.gregs[1] = value.to_u32() as u64,
            Arm64Reg::w2 => self.regs.gregs[2] = value.to_u32() as u64,
            Arm64Reg::w3 => self.regs.gregs[3] = value.to_u32() as u64,
            Arm64Reg::w4 => self.regs.gregs[4] = value.to_u32() as u64,
            Arm64Reg::w5 => self.regs.gregs[5] = value.to_u32() as u64,
            Arm64Reg::w6 => self.regs.gregs[6] = value.to_u32() as u64,
            Arm64Reg::w7 => self.regs.gregs[7] = value.to_u32() as u64,
            Arm64Reg::w8 => self.regs.gregs[8] = value.to_u32() as u64,
            Arm64Reg::w9 => self.regs.gregs[9] = value.to_u32() as u64,
            Arm64Reg::w10 => self.regs.gregs[10] = value.to_u32() as u64,
            Arm64Reg::w11 => self.regs.gregs[11] = value.to_u32() as u64,
            Arm64Reg::w12 => self.regs.gregs[12] = value.to_u32() as u64,
            Arm64Reg::w13 => self.regs.gregs[13] = value.to_u32() as u64,
            Arm64Reg::w14 => self.regs.gregs[14] = value.to_u32() as u64,
            Arm64Reg::w15 => self.regs.gregs[15] = value.to_u32() as u64,
            Arm64Reg::w16 => self.regs.gregs[16] = value.to_u32() as u64,
            Arm64Reg::w17 => self.regs.gregs[17] = value.to_u32() as u64,
            Arm64Reg::w18 => self.regs.gregs[18] = value.to_u32() as u64,
            Arm64Reg::w19 => self.regs.gregs[19] = value.to_u32() as u64,
            Arm64Reg::w20 => self.regs.gregs[20] = value.to_u32() as u64,
            Arm64Reg::w21 => self.regs.gregs[21] = value.to_u32() as u64,
            Arm64Reg::w22 => self.regs.gregs[22] = value.to_u32() as u64,
            Arm64Reg::w23 => self.regs.gregs[23] = value.to_u32() as u64,
            Arm64Reg::w24 => self.regs.gregs[24] = value.to_u32() as u64,
            Arm64Reg::w25 => self.regs.gregs[25] = value.to_u32() as u64,
            Arm64Reg::w26 => self.regs.gregs[26] = value.to_u32() as u64,
            Arm64Reg::w27 => self.regs.gregs[27] = value.to_u32() as u64,
            Arm64Reg::w28 => self.regs.gregs[28] = value.to_u32() as u64,
            Arm64Reg::w29 => self.regs.gregs[29] = value.to_u32() as u64,
            Arm64Reg::w30 => self.regs.gregs[30] = value.to_u32() as u64,
            Arm64Reg::wsp => self.regs.gregs[31] = value.to_u32() as u64,
            Arm64Reg::x0 => self.regs.gregs[0] = value.extend_64(),
            Arm64Reg::x1 => self.regs.gregs[1] = value.extend_64(),
            Arm64Reg::x2 => self.regs.gregs[2] = value.extend_64(),
            Arm64Reg::x3 => self.regs.gregs[3] = value.extend_64(),
            Arm64Reg::x4 => self.regs.gregs[4] = value.extend_64(),
            Arm64Reg::x5 => self.regs.gregs[5] = value.extend_64(),
            Arm64Reg::x6 => self.regs.gregs[6] = value.extend_64(),
            Arm64Reg::x7 => self.regs.gregs[7] = value.extend_64(),
            Arm64Reg::x8 => self.regs.gregs[8] = value.extend_64(),
            Arm64Reg::x9 => self.regs.gregs[9] = value.extend_64(),
            Arm64Reg::x10 => self.regs.gregs[10] = value.extend_64(),
            Arm64Reg::x11 => self.regs.gregs[11] = value.extend_64(),
            Arm64Reg::x12 => self.regs.gregs[12] = value.extend_64(),
            Arm64Reg::x13 => self.regs.gregs[13] = value.extend_64(),
            Arm64Reg::x14 => self.regs.gregs[14] = value.extend_64(),
            Arm64Reg::x15 => self.regs.gregs[15] = value.extend_64(),
            Arm64Reg::x16 => self.regs.gregs[16] = value.extend_64(),
            Arm64Reg::x17 => self.regs.gregs[17] = value.extend_64(),
            Arm64Reg::x18 => self.regs.gregs[18] = value.extend_64(),
            Arm64Reg::x19 => self.regs.gregs[19] = value.extend_64(),
            Arm64Reg::x20 => self.regs.gregs[20] = value.extend_64(),
            Arm64Reg::x21 => self.regs.gregs[21] = value.extend_64(),
            Arm64Reg::x22 => self.regs.gregs[22] = value.extend_64(),
            Arm64Reg::x23 => self.regs.gregs[23] = value.extend_64(),
            Arm64Reg::x24 => self.regs.gregs[24] = value.extend_64(),
            Arm64Reg::x25 => self.regs.gregs[25] = value.extend_64(),
            Arm64Reg::x26 => self.regs.gregs[26] = value.extend_64(),
            Arm64Reg::x27 => self.regs.gregs[27] = value.extend_64(),
            Arm64Reg::x28 => self.regs.gregs[28] = value.extend_64(),
            Arm64Reg::fp => self.regs.gregs[29] = value.extend_64(),
            Arm64Reg::lr => self.regs.gregs[30] = value.extend_64(),
            Arm64Reg::sp => self.regs.gregs[31] = value.extend_64(),
            Arm64Reg::syscall_info => self.regs.syscall_info = value.extend_64(),
        };
    }

    fn read_mem(&self, addr: u64, buf: &mut [u8]) -> Result<(), softmew::fault::Fault> {
        self.mem.read_perm(addr as usize, buf)
    }

    fn write_mem(&mut self, addr: u64, data: &[u8]) -> Result<(), softmew::fault::Fault> {
        self.mem.write_perm(addr as usize, data)
    }

    fn get_flag(&self, id: u32) -> bool {
        if id < 32 {
            ((self.flag >> id) & 0b1) != 0
        } else {
            (self.conds[(id - 0x80000000) as usize]) != 0
        }
    }

    fn set_flag(&mut self, val: bool, id: u32) {
        if id < 32 {
            self.flag &= !((1u64) << id);
            self.flag |= (val as u64) << id;
        } else {
            self.conds[(id - 0x80000000) as usize] = val as u8;
        }
    }

    fn save_ret_addr(&mut self, addr: u64) -> Result<(), softmew::fault::Fault> {
        self.regs[Arm64Reg::lr] = addr;
        Ok(())
    }

    fn push(&mut self, val: &[u8]) -> Result<(), softmew::fault::Fault> {
        let mut sp = self.regs[Arm64Reg::sp];
        sp -= val.len() as u64;
        self.regs[Arm64Reg::sp] = sp;
        self.mem.write_perm(sp as usize, val)
    }

    fn pop(&mut self, data: &mut [u8]) -> Result<(), softmew::fault::Fault> {
        let sp = self.regs[Arm64Reg::sp];
        self.regs[Arm64Reg::sp] = sp - data.len() as u64;
        self.mem.read_perm(sp as usize, data)
    }

    fn intrinsic(&mut self, intrin: &ArmIntrinsic) -> Result<(), softmew::fault::Fault> {
        match intrin {
            ArmIntrinsic::Dmb => Ok(()),
            ArmIntrinsic::ReadMSR(reg, msr) => {
                match msr {
                    0xd807 => {
                        // DCZID_EL0 system register
                        self.write_reg(*reg, ILVal::Quad(0b10000));
                        Ok(())
                    }
                    0xc000 => {
                        // MIDR_EL1, Main ID Register
                        self.write_reg(*reg, ILVal::Quad(0b00000000_0000_1111_000000000000_0000));
                        Ok(())
                    }
                    0xde82 => {
                        // TPIDR_EL0, Thread ID Register
                        self.regs[*reg] = self.tpid;
                        Ok(())
                    }
                    x => panic!("Implement reading msr {x:#x}"),
                }
            }
            ArmIntrinsic::WriteMSR(reg, msr) => {
                match msr {
                    0xde82 => {
                        // TPIDR_EL0, Thread ID Register
                        self.tpid = self.regs[*reg];
                        Ok(())
                    }
                    x => panic!("Implement writing msr {x:#x}"),
                }
            }
        }
    }

    fn syscall(&mut self, _addr: u64) -> super::SyscallResult {
        let syscall_no = self.regs.gregs[8] as u32;
        syscalls!(
            self,
            syscall_no,
            (0x38, openat),
            (0x3f, read),
            (0x40, write),
            (0x4e, readlinkat),
            (0x60, set_tid_address),
            (0x63, set_robust_list),
            (0xae, getuid),
            (0xa0, uname),
            (0xaf, geteuid),
            (0xb0, getgid),
            (0xb1, getegid),
            (0xd6, brk),
            (0x105, prlimit64),
            (0x125, rseq)
        )
    }
}

#[derive(Default, Clone, Copy, Debug)]
pub struct Arm64State {
    gregs: [u64; 32],
    syscall_info: u64,
}

impl RegState for Arm64State {
    fn set_syscall_return(&mut self, val: ILVal) {
        self[Arm64Reg::x0] = val.extend_64()
    }
}

impl Arm64State {
    pub fn get(&self, reg: Arm64Reg) -> ILVal {
        match reg {
            Arm64Reg::w0 => ILVal::Word(self.gregs[0] as u32),
            Arm64Reg::w1 => ILVal::Word(self.gregs[1] as u32),
            Arm64Reg::w2 => ILVal::Word(self.gregs[2] as u32),
            Arm64Reg::w3 => ILVal::Word(self.gregs[3] as u32),
            Arm64Reg::w4 => ILVal::Word(self.gregs[4] as u32),
            Arm64Reg::w5 => ILVal::Word(self.gregs[5] as u32),
            Arm64Reg::w6 => ILVal::Word(self.gregs[6] as u32),
            Arm64Reg::w7 => ILVal::Word(self.gregs[7] as u32),
            Arm64Reg::w8 => ILVal::Word(self.gregs[8] as u32),
            Arm64Reg::w9 => ILVal::Word(self.gregs[9] as u32),
            Arm64Reg::w10 => ILVal::Word(self.gregs[10] as u32),
            Arm64Reg::w11 => ILVal::Word(self.gregs[11] as u32),
            Arm64Reg::w12 => ILVal::Word(self.gregs[12] as u32),
            Arm64Reg::w13 => ILVal::Word(self.gregs[13] as u32),
            Arm64Reg::w14 => ILVal::Word(self.gregs[14] as u32),
            Arm64Reg::w15 => ILVal::Word(self.gregs[15] as u32),
            Arm64Reg::w16 => ILVal::Word(self.gregs[16] as u32),
            Arm64Reg::w17 => ILVal::Word(self.gregs[17] as u32),
            Arm64Reg::w18 => ILVal::Word(self.gregs[18] as u32),
            Arm64Reg::w19 => ILVal::Word(self.gregs[19] as u32),
            Arm64Reg::w20 => ILVal::Word(self.gregs[20] as u32),
            Arm64Reg::w21 => ILVal::Word(self.gregs[21] as u32),
            Arm64Reg::w22 => ILVal::Word(self.gregs[22] as u32),
            Arm64Reg::w23 => ILVal::Word(self.gregs[23] as u32),
            Arm64Reg::w24 => ILVal::Word(self.gregs[24] as u32),
            Arm64Reg::w25 => ILVal::Word(self.gregs[25] as u32),
            Arm64Reg::w26 => ILVal::Word(self.gregs[26] as u32),
            Arm64Reg::w27 => ILVal::Word(self.gregs[27] as u32),
            Arm64Reg::w28 => ILVal::Word(self.gregs[28] as u32),
            Arm64Reg::w29 => ILVal::Word(self.gregs[29] as u32),
            Arm64Reg::w30 => ILVal::Word(self.gregs[30] as u32),
            Arm64Reg::wsp => ILVal::Word(self.gregs[31] as u32),
            Arm64Reg::x0 => ILVal::Quad(self.gregs[0]),
            Arm64Reg::x1 => ILVal::Quad(self.gregs[1]),
            Arm64Reg::x2 => ILVal::Quad(self.gregs[2]),
            Arm64Reg::x3 => ILVal::Quad(self.gregs[3]),
            Arm64Reg::x4 => ILVal::Quad(self.gregs[4]),
            Arm64Reg::x5 => ILVal::Quad(self.gregs[5]),
            Arm64Reg::x6 => ILVal::Quad(self.gregs[6]),
            Arm64Reg::x7 => ILVal::Quad(self.gregs[7]),
            Arm64Reg::x8 => ILVal::Quad(self.gregs[8]),
            Arm64Reg::x9 => ILVal::Quad(self.gregs[9]),
            Arm64Reg::x10 => ILVal::Quad(self.gregs[10]),
            Arm64Reg::x11 => ILVal::Quad(self.gregs[11]),
            Arm64Reg::x12 => ILVal::Quad(self.gregs[12]),
            Arm64Reg::x13 => ILVal::Quad(self.gregs[13]),
            Arm64Reg::x14 => ILVal::Quad(self.gregs[14]),
            Arm64Reg::x15 => ILVal::Quad(self.gregs[15]),
            Arm64Reg::x16 => ILVal::Quad(self.gregs[16]),
            Arm64Reg::x17 => ILVal::Quad(self.gregs[17]),
            Arm64Reg::x18 => ILVal::Quad(self.gregs[18]),
            Arm64Reg::x19 => ILVal::Quad(self.gregs[19]),
            Arm64Reg::x20 => ILVal::Quad(self.gregs[20]),
            Arm64Reg::x21 => ILVal::Quad(self.gregs[21]),
            Arm64Reg::x22 => ILVal::Quad(self.gregs[22]),
            Arm64Reg::x23 => ILVal::Quad(self.gregs[23]),
            Arm64Reg::x24 => ILVal::Quad(self.gregs[24]),
            Arm64Reg::x25 => ILVal::Quad(self.gregs[25]),
            Arm64Reg::x26 => ILVal::Quad(self.gregs[26]),
            Arm64Reg::x27 => ILVal::Quad(self.gregs[27]),
            Arm64Reg::x28 => ILVal::Quad(self.gregs[28]),
            Arm64Reg::fp => ILVal::Quad(self.gregs[29]),
            Arm64Reg::lr => ILVal::Quad(self.gregs[30]),
            Arm64Reg::sp => ILVal::Quad(self.gregs[31]),
            Arm64Reg::syscall_info => ILVal::Quad(self.syscall_info),
        }
    }
}

impl Index<Arm64Reg> for Arm64State {
    type Output = u64;

    fn index(&self, index: Arm64Reg) -> &Self::Output {
        match index {
            Arm64Reg::x0 => &self.gregs[0],
            Arm64Reg::x1 => &self.gregs[1],
            Arm64Reg::x2 => &self.gregs[2],
            Arm64Reg::x3 => &self.gregs[3],
            Arm64Reg::x4 => &self.gregs[4],
            Arm64Reg::x5 => &self.gregs[5],
            Arm64Reg::x6 => &self.gregs[6],
            Arm64Reg::x7 => &self.gregs[7],
            Arm64Reg::x8 => &self.gregs[8],
            Arm64Reg::x9 => &self.gregs[9],
            Arm64Reg::x10 => &self.gregs[10],
            Arm64Reg::x11 => &self.gregs[11],
            Arm64Reg::x12 => &self.gregs[12],
            Arm64Reg::x13 => &self.gregs[13],
            Arm64Reg::x14 => &self.gregs[14],
            Arm64Reg::x15 => &self.gregs[15],
            Arm64Reg::x16 => &self.gregs[16],
            Arm64Reg::x17 => &self.gregs[17],
            Arm64Reg::x18 => &self.gregs[18],
            Arm64Reg::x19 => &self.gregs[19],
            Arm64Reg::x20 => &self.gregs[20],
            Arm64Reg::x21 => &self.gregs[21],
            Arm64Reg::x22 => &self.gregs[22],
            Arm64Reg::x23 => &self.gregs[23],
            Arm64Reg::x24 => &self.gregs[24],
            Arm64Reg::x25 => &self.gregs[25],
            Arm64Reg::x26 => &self.gregs[26],
            Arm64Reg::x27 => &self.gregs[27],
            Arm64Reg::x28 => &self.gregs[28],
            Arm64Reg::fp => &self.gregs[29],
            Arm64Reg::lr => &self.gregs[30],
            Arm64Reg::sp => &self.gregs[31],
            Arm64Reg::syscall_info => &self.syscall_info,
            _ => panic!("Can only index full sized registers"),
        }
    }
}

impl IndexMut<Arm64Reg> for Arm64State {
    fn index_mut(&mut self, index: Arm64Reg) -> &mut Self::Output {
        match index {
            Arm64Reg::x0 => &mut self.gregs[0],
            Arm64Reg::x1 => &mut self.gregs[1],
            Arm64Reg::x2 => &mut self.gregs[2],
            Arm64Reg::x3 => &mut self.gregs[3],
            Arm64Reg::x4 => &mut self.gregs[4],
            Arm64Reg::x5 => &mut self.gregs[5],
            Arm64Reg::x6 => &mut self.gregs[6],
            Arm64Reg::x7 => &mut self.gregs[7],
            Arm64Reg::x8 => &mut self.gregs[8],
            Arm64Reg::x9 => &mut self.gregs[9],
            Arm64Reg::x10 => &mut self.gregs[10],
            Arm64Reg::x11 => &mut self.gregs[11],
            Arm64Reg::x12 => &mut self.gregs[12],
            Arm64Reg::x13 => &mut self.gregs[13],
            Arm64Reg::x14 => &mut self.gregs[14],
            Arm64Reg::x15 => &mut self.gregs[15],
            Arm64Reg::x16 => &mut self.gregs[16],
            Arm64Reg::x17 => &mut self.gregs[17],
            Arm64Reg::x18 => &mut self.gregs[18],
            Arm64Reg::x19 => &mut self.gregs[19],
            Arm64Reg::x20 => &mut self.gregs[20],
            Arm64Reg::x21 => &mut self.gregs[21],
            Arm64Reg::x22 => &mut self.gregs[22],
            Arm64Reg::x23 => &mut self.gregs[23],
            Arm64Reg::x24 => &mut self.gregs[24],
            Arm64Reg::x25 => &mut self.gregs[25],
            Arm64Reg::x26 => &mut self.gregs[26],
            Arm64Reg::x27 => &mut self.gregs[27],
            Arm64Reg::x28 => &mut self.gregs[28],
            Arm64Reg::fp => &mut self.gregs[29],
            Arm64Reg::lr => &mut self.gregs[30],
            Arm64Reg::sp => &mut self.gregs[31],
            Arm64Reg::syscall_info => &mut self.syscall_info,
            _ => panic!("Can only index full sized registers"),
        }
    }
}

#[allow(non_camel_case_types)]
#[repr(u32)]
#[derive(FromId, Debug, Clone, Copy, PartialEq, Eq)]
pub enum Arm64Reg {
    w0 = 1,
    w1 = 2,
    w2 = 3,
    w3 = 4,
    w4 = 5,
    w5 = 6,
    w6 = 7,
    w7 = 8,
    w8 = 9,
    w9 = 10,
    w10 = 11,
    w11 = 12,
    w12 = 13,
    w13 = 14,
    w14 = 15,
    w15 = 16,
    w16 = 17,
    w17 = 18,
    w18 = 19,
    w19 = 20,
    w20 = 21,
    w21 = 22,
    w22 = 23,
    w23 = 24,
    w24 = 25,
    w25 = 26,
    w26 = 27,
    w27 = 28,
    w28 = 29,
    w29 = 30,
    w30 = 31,
    wsp = 33,
    x0 = 34,
    x1 = 35,
    x2 = 36,
    x3 = 37,
    x4 = 38,
    x5 = 39,
    x6 = 40,
    x7 = 41,
    x8 = 42,
    x9 = 43,
    x10 = 44,
    x11 = 45,
    x12 = 46,
    x13 = 47,
    x14 = 48,
    x15 = 49,
    x16 = 50,
    x17 = 51,
    x18 = 52,
    x19 = 53,
    x20 = 54,
    x21 = 55,
    x22 = 56,
    x23 = 57,
    x24 = 58,
    x25 = 59,
    x26 = 60,
    x27 = 61,
    x28 = 62,
    fp = 63,
    lr = 64,
    sp = 66,
    syscall_info = 65534,
}

impl Register for Arm64Reg {
    fn syscall_ret() -> Self {
        Self::x0
    }
}

impl std::fmt::Display for Arm64Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

/// Basic linux state for an Arm64 machine.
///
/// Implements the basic system calls and will keep track of stdin, stdout, and stderr state.
pub struct ArmMachine {
    fds: HashMap<u32, Box<dyn FileDescriptor>>,
    heap: Range<u64>,
}

impl ArmMachine {
    /// Create a new machine with initially empty stdin, stdout, and stderr.
    ///
    /// `heap` is the range of addresses that should be used for the heap. Those addresses are used to set return values for
    /// the brk syscall.
    pub fn new(heap: Range<u64>) -> Self {
        let mut map = HashMap::new();
        let stdin: Box<dyn FileDescriptor> = Box::new(VecDeque::<u8>::new());
        let stdout: Box<dyn FileDescriptor> = Box::new(VecDeque::<u8>::new());
        let stderr: Box<dyn FileDescriptor> = Box::new(VecDeque::<u8>::new());
        map.insert(0, stdin);
        map.insert(1, stdout);
        map.insert(2, stderr);
        Self { fds: map, heap }
    }

    pub fn take_fd(&mut self, fd: u32) -> Option<Box<dyn FileDescriptor>> {
        self.fds.remove(&fd)
    }

    pub fn set_stdin<T: FileDescriptor>(&mut self, data: T) -> Option<Box<dyn FileDescriptor>> {
        let stdin = Box::new(data);
        self.fds.insert(0, stdin)
    }

    pub fn get_fd(&self, fd: u32) -> Option<&dyn FileDescriptor> {
        self.fds.get(&fd).map(|f| f.as_ref())
    }

    pub fn get_fd_mut(&mut self, fd: u32) -> Option<&mut dyn FileDescriptor> {
        self.fds.get_mut(&fd).map(|f| f.as_mut())
    }
}

impl LinuxSyscalls<Arm64State, MMU<SimplePage>> for ArmMachine {
    fn read(&mut self, regs: &mut Arm64State, mem: &mut MMU<SimplePage>) -> SyscallResult {
        let fd = regs[Arm64Reg::x0];
        let ptr = regs[Arm64Reg::x1] as usize;
        let len = regs[Arm64Reg::x2] as usize;
        match self.fds.get_mut(&(fd as u32)) {
            Some(file) => {
                let page = mem.get_mapping_mut(ptr).unwrap();
                let start = page.start();
                let buf = &mut page.as_mut()[ptr - start..][..len];
                let res = file.read(buf);
                match res {
                    Ok(b) => regs[Arm64Reg::x0] = b as u64,
                    Err(e) => {
                        regs[Arm64Reg::x0] = e.raw_os_error().unwrap_or(-9) as u64;
                    }
                }
            }
            None => regs[Arm64Reg::x0] = (-9_i64) as u64,
        };
        SyscallResult::Continue
    }

    fn write(&mut self, regs: &mut Arm64State, mem: &mut MMU<SimplePage>) -> SyscallResult {
        let fd = regs[Arm64Reg::x0];
        let ptr = regs[Arm64Reg::x1];
        let len = regs[Arm64Reg::x2];
        let mut data = vec![0; len as usize];
        mem.read_perm(ptr as usize, &mut data)
            .expect("Failed to read message");
        match self.fds.get_mut(&(fd as u32)) {
            Some(file) => {
                let res = file.write(&data);
                match res {
                    Ok(b) => regs[Arm64Reg::x0] = b as u64,
                    Err(e) => {
                        regs[Arm64Reg::x0] = e.raw_os_error().unwrap_or(-9) as u64;
                    }
                }
            }
            None => regs[Arm64Reg::x0] = len,
        }
        SyscallResult::Continue
    }

    fn set_tid_address(
        &mut self,
        regs: &mut Arm64State,
        _mem: &mut MMU<SimplePage>,
    ) -> SyscallResult {
        regs[Arm64Reg::x0] = 100;
        SyscallResult::Continue
    }

    fn set_robust_list(
        &mut self,
        regs: &mut Arm64State,
        _mem: &mut MMU<SimplePage>,
    ) -> SyscallResult {
        regs[Arm64Reg::x0] = 0;
        SyscallResult::Continue
    }

    fn uname(&mut self, regs: &mut Arm64State, mem: &mut MMU<SimplePage>) -> SyscallResult {
        let addr = regs[Arm64Reg::x0];
        regs[Arm64Reg::x0] = (-14_i64) as u64;
        if mem.write_perm(addr as usize, b"Linux\x00").is_err() {
            println!("linux failed");
            return SyscallResult::Continue;
        }
        if mem
            .write_perm((addr + 65) as usize, b"binja-emu\x00")
            .is_err()
        {
            println!("binja-emu failed");
            return SyscallResult::Continue;
        }
        if mem
            .write_perm((addr + 65 * 2) as usize, b"6.16.3-76061603-generic\x00")
            .is_err()
        {
            println!("release failed");
            return SyscallResult::Continue;
        }
        if mem
            .write_perm(
                (addr + 65 * 3) as usize,
                b"#202508231538~1758561135~22.04~171c8de\x00",
            )
            .is_err()
        {
            println!("version failed");
            return SyscallResult::Continue;
        }
        if mem
            .write_perm((addr + 65 * 4) as usize, b"aarch64\x00")
            .is_err()
        {
            println!("arch failed");
            return SyscallResult::Continue;
        }
        if mem
            .write_perm((addr + 65 * 5) as usize, b"binja.emu\x00")
            .is_err()
        {
            println!("domain failed");
            return SyscallResult::Continue;
        }
        regs[Arm64Reg::x0] = 0;
        SyscallResult::Continue
    }

    fn getrandom(&mut self, regs: &mut Arm64State, mem: &mut MMU<SimplePage>) -> SyscallResult {
        let addr = regs[Arm64Reg::x0];
        let size = regs[Arm64Reg::x1];
        regs[Arm64Reg::x0] = (-14_i64) as u64;
        for i in addr..(addr + size) {
            if mem.write_perm(i as usize, &[0xee]).is_err() {
                return SyscallResult::Continue;
            }
        }

        regs[Arm64Reg::x0] = 0;
        SyscallResult::Continue
    }

    fn getuid(&mut self, regs: &mut Arm64State, _mem: &mut MMU<SimplePage>) -> SyscallResult {
        regs[Arm64Reg::x0] = 1000;
        SyscallResult::Continue
    }

    fn geteuid(&mut self, regs: &mut Arm64State, _mem: &mut MMU<SimplePage>) -> SyscallResult {
        regs[Arm64Reg::x0] = 1000;
        SyscallResult::Continue
    }

    fn getgid(&mut self, regs: &mut Arm64State, _mem: &mut MMU<SimplePage>) -> SyscallResult {
        regs[Arm64Reg::x0] = 1000;
        SyscallResult::Continue
    }

    fn getegid(&mut self, regs: &mut Arm64State, _mem: &mut MMU<SimplePage>) -> SyscallResult {
        regs[Arm64Reg::x0] = 1000;
        SyscallResult::Continue
    }

    fn brk(&mut self, regs: &mut Arm64State, _mem: &mut MMU<SimplePage>) -> SyscallResult {
        let addr = regs[Arm64Reg::x0];
        if addr < self.heap.start {
            regs[Arm64Reg::x0] = self.heap.start;
        } else if addr > self.heap.end {
            regs[Arm64Reg::x0] = self.heap.end;
        }
        SyscallResult::Continue
    }

    fn mmap(&mut self, regs: &mut Arm64State, mem: &mut MMU<SimplePage>) -> SyscallResult {
        let addr = regs[Arm64Reg::x0];
        let len = regs[Arm64Reg::x1];

        if addr != 0 {
            // Just map at any address that has the required size
            let range = mem.gaps().find(|r| r.size() >= len as usize);
            if let Some(addrs) = range {
                let page = mem.map_memory(addrs.start, len as usize, Perm::READ | Perm::WRITE);
                if page.is_ok() {
                    regs[Arm64Reg::x0] = addrs.start as u64;
                    return SyscallResult::Continue;
                }
            }
            regs[Arm64Reg::x0] = u64::MAX;
            return SyscallResult::Continue;
        } else {
            let page = mem.map_memory(addr as usize, len as usize, Perm::READ | Perm::WRITE);
            if page.is_ok() {
                regs[Arm64Reg::x0] = addr;
                return SyscallResult::Continue;
            }
            regs[Arm64Reg::x0] = u64::MAX;
            return SyscallResult::Continue;
        }
    }

    fn writev(&mut self, regs: &mut Arm64State, _mem: &mut MMU<SimplePage>) -> SyscallResult {
        let _fd = regs[Arm64Reg::x0];
        let _iov = regs[Arm64Reg::x1];
        let _iocnt = regs[Arm64Reg::x2];
        SyscallResult::Continue
    }

    fn readlinkat(&mut self, regs: &mut Arm64State, mem: &mut MMU<SimplePage>) -> SyscallResult {
        let mut path_addr = regs[Arm64Reg::x1];
        let mut path = Vec::new();
        let mut buf = [0u8];
        let link_buf = regs[Arm64Reg::x2];
        loop {
            if mem.read_perm(path_addr as usize, &mut buf).is_err() {
                regs[Arm64Reg::x0] = (-14_i64) as u64;
                return SyscallResult::Continue;
            }
            if buf[0] == 0 {
                break;
            }
            path.push(buf[0]);
            path_addr += 1;
        }
        match <Vec<u8> as AsRef<[u8]>>::as_ref(&path) {
            b"/proc/self/exe" => {
                mem.write_perm(link_buf as usize, b"/home/project/read-stdin\x00");
                regs[Arm64Reg::x0] = 24;
            }
            _ => regs[Arm64Reg::x0] = (-2_i64) as u64,
        }
        SyscallResult::Continue
    }
}
