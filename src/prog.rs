use crate::arch::Register as Reg;
use crate::emil::{Emil, ILRef};
use crate::emulate::Endian;
use binaryninja::architecture::Register as _;
use binaryninja::low_level_il::expression::{
    ExpressionHandler, LowLevelILExpression as Expr, LowLevelILExpressionKind as ExprKind,
    ValueExpr,
};
use binaryninja::low_level_il::function::{Finalized, LowLevelILFunction, NonSSA};
use binaryninja::low_level_il::instruction::{
    InstructionHandler, LowLevelInstructionIndex as LLILIdx,
};
use binaryninja::low_level_il::instruction::{
    LowLevelILInstruction as Instruction, LowLevelILInstructionKind as Kind,
};
use std::collections::HashMap;

/// Helper type to describe an LLIL function in non-ssa finalized form
type LLILFunc = LowLevelILFunction<Finalized, NonSSA>;
/// Helper type to describe an LLIL instruction in non-ssa finalized form
type LLILInsn<'i> = Instruction<'i, Finalized, NonSSA>;
/// Helper type to describe an LLIL expression in non-ssa finalized form
type LLILExpr<'e> = Expr<'e, Finalized, NonSSA, ValueExpr>;

const TEMP_BIT: u32 = 0b10000000_00000000_00000000_00000000;

pub struct Program<R: Reg, E: Endian> {
    /// List of all [`Emil`] instructions in order
    pub(crate) il: Vec<Emil<R, E>>,
    /// Map of architecture instruction address to index of the first IL instruction that implements it
    pub(crate) insn_map: HashMap<u64, usize>,
    /// Map of il instruction index to program address.
    pub(crate) addr_map: Vec<u64>,
}

impl<R: Reg, E: Endian> Default for Program<R, E> {
    fn default() -> Self {
        Self {
            il: Vec::new(),
            insn_map: HashMap::new(),
            addr_map: Vec::new(),
        }
    }
}

macro_rules! bin_op {
    ($op:ident, $instr:ident, $prog:ident, $ilr:ident) => {{
        let left = $prog.add_expr(&$op.left(), $ilr);
        let right = $prog.add_expr(&$op.right(), left.next());
        let out = right.next();
        $prog.il.push(Emil::$instr { out, left, right });
        out
    }};
}

impl<R: Reg, E: Endian> Program<R, E> {
    pub fn add_function(&mut self, func: &LLILFunc) {
        // The jump instructions will need to be fixed up after they are added. LLIL encodes those
        // as jumping to an address or going to a specific LLIL index. The instructions here will
        // only understand jumping to specific indexes in the array. After they have been added,
        // they will need to be fixed up after the fact.
        //
        // Jump and call instructions may not be relocatable. So just the goto instructions should
        // be updated here and the call instructions will be updated later.
        let addr = func.function().start();
        self.insn_map.insert(addr, self.il.len());
        let num_insns = func.instruction_count();
        if num_insns == 0 {
            return;
        }
        // Map a llil idx to the first il index that corresponds to it.
        let mut llil_map = Vec::new();
        let start = self.il.len();
        for idx in 0..num_insns {
            llil_map.push(self.il.len());
            let llil = func
                .instruction_from_index(LLILIdx(idx))
                .expect("This index is in bounds");
            let prog_addr = llil.address();
            self.insn_map.entry(prog_addr).or_insert(self.il.len());
            // self.insn_map.insert(llil.address(), self.il.len());
            self.add_instruction(&llil);
            while self.addr_map.len() != self.il.len() {
                self.addr_map.push(prog_addr);
            }
        }
        for reloc in &mut self.il[start..] {
            if let Emil::Goto(addr) = reloc {
                *addr = *llil_map.get(*addr).expect("Invalid goto in program");
            } else if let Emil::If {
                true_target,
                false_target,
                ..
            } = reloc
            {
                *true_target = *llil_map.get(*true_target).expect("Invalid goto in binary");
                *false_target = *llil_map.get(*false_target).expect("Invalid goto in binary");
            }
        }
    }

    /// Add a single LLIL instruction to the program.
    fn add_instruction(&mut self, insn: &LLILInsn<'_>) {
        match insn.kind() {
            Kind::Nop(_) => self.il.push(Emil::Nop),
            Kind::Syscall(_) | Kind::SyscallSsa(_) => self.il.push(Emil::Syscall),
            Kind::NoRet(_) => self.il.push(Emil::NoRet),
            Kind::Bp(_) => self.il.push(Emil::Bp),
            Kind::Undef(_) => self.il.push(Emil::Undef),
            Kind::Intrinsic(i) => self.il.push(Emil::Intrinsic(
                i.intrinsic().expect("Unknown intrinsic").id.0,
            )),
            Kind::Trap(t) => self.il.push(Emil::Trap(t.vector())),
            Kind::SetReg(sr) => {
                let ilr = self.add_expr(&sr.source_expr(), ILRef(0));
                match sr.dest_reg() {
                    binaryninja::low_level_il::LowLevelILRegisterKind::Arch(a) => {
                        let arch_reg = R::try_from(a.id().0)
                            .map_err(|_| format!("Invalid id {}", sr.dest_reg().id().0))
                            .expect("Invalid architecture register in program");
                        self.il.push(Emil::SetReg { reg: arch_reg, ilr });
                    }
                    binaryninja::low_level_il::LowLevelILRegisterKind::Temp(t) => {
                        let id: u8 = (t.id().0 ^ TEMP_BIT)
                            .try_into()
                            .expect("Invalid temporary ID");
                        self.il.push(Emil::SetTemp { t: id, ilr });
                    }
                }
            }
            Kind::If(conditional) => {
                let condition = self.add_expr(&conditional.condition(), ILRef(0));
                let true_target = conditional.true_target().index.0;
                let false_target = conditional.false_target().index.0;
                self.il.push(Emil::If {
                    condition,
                    true_target,
                    false_target,
                });
            }
            Kind::Call(c) => {
                let dest = self.add_expr(&c.target(), ILRef(0));
                self.il.push(Emil::Call {
                    target: dest,
                    // stack: c.stack_adjust().expect("Unknown stack adjustment"),
                    stack: c.stack_adjust().unwrap_or(0),
                });
            }
            Kind::Ret(r) => {
                let dest = self.add_expr(&r.target(), ILRef(0));
                self.il.push(Emil::Ret(dest));
            }
            Kind::TailCall(tc) => {
                let dest = self.add_expr(&tc.target(), ILRef(0));
                self.il.push(Emil::TailCall {
                    target: dest,
                    stack: tc.stack_adjust().unwrap_or(0),
                });
            }
            Kind::Goto(idx) => self.il.push(Emil::Goto(idx.target().index.0)),
            Kind::Jump(j) => {
                let dest = self.add_expr(&j.target(), ILRef(0));
                self.il.push(Emil::Jump(dest))
            }
            Kind::JumpTo(jt) => {
                let dest = self.add_expr(&jt.target(), ILRef(0));
                self.il.push(Emil::Jump(dest));
            }
            Kind::Store(mem_write) => {
                let source = self.add_expr(&mem_write.source_expr(), ILRef(0));
                let dest = self.add_expr(&mem_write.dest_expr(), source.next());
                match mem_write.size() {
                    1 => self.il.push(Emil::Store {
                        value: source,
                        addr: dest,
                    }),
                    2 => self.il.push(Emil::Store {
                        value: source,
                        addr: dest,
                    }),
                    4 => self.il.push(Emil::Store {
                        value: source,
                        addr: dest,
                    }),
                    8 => self.il.push(Emil::Store {
                        value: source,
                        addr: dest,
                    }),
                    s => panic!("Invalid memory write size of {s} bytes"),
                }
            }
            Kind::Push(p) => {
                let value = self.add_expr(&p.operand(), ILRef(0));
                self.il.push(Emil::Push(value));
            }
            _ => unimplemented!(
                "Encountered unimplemented instruction kind: {:?} 0x{:X}",
                insn,
                insn.address()
            ),
        }
    }

    /// Parse an expression tree into the intermediate language.
    ///
    /// Returns the ILR register that holds the result of the expression.
    fn add_expr(&mut self, expr: &LLILExpr<'_>, ilr: ILRef) -> ILRef {
        match expr.kind() {
            ExprKind::Unimpl(_) | ExprKind::UnimplMem(_) => {
                self.il.push(Emil::Undef);
                ilr
            }
            ExprKind::Undef(_) => {
                self.il.push(Emil::Undef);
                ilr
            }
            ExprKind::Reg(r) => match r.source_reg() {
                binaryninja::low_level_il::LowLevelILRegisterKind::Arch(a) => {
                    let arch_reg = R::try_from(a.id().0)
                        .map_err(|_| format!("Invalid id {}", r.source_reg().id().0))
                        .expect("Invalid arch register");
                    self.il.push(Emil::LoadReg { reg: arch_reg, ilr });
                    ilr
                }
                binaryninja::low_level_il::LowLevelILRegisterKind::Temp(t) => {
                    let id: u8 = (t.id().0 ^ TEMP_BIT)
                        .try_into()
                        .expect("Invalid temporary register id");
                    self.il.push(Emil::LoadTemp { ilr, t: id });
                    ilr
                }
            },
            ExprKind::Const(c) | ExprKind::ConstPtr(c) => {
                let value = c.value();
                let size = match c.size() {
                    1 => 1,
                    2 => 2,
                    4 => 4,
                    8 => 8,
                    _ => panic!("Invalid constant size"),
                };
                self.il.push(Emil::Constant {
                    reg: ilr,
                    value,
                    size,
                });
                ilr
            }
            ExprKind::Load(l) => {
                let addr = self.add_expr(&l.source_expr(), ilr);
                let dest = addr.next();
                match l.size() {
                    1 => {
                        self.il.push(Emil::Load {
                            dest,
                            addr,
                            size: 1,
                        });
                        dest
                    }
                    2 => {
                        self.il.push(Emil::Load {
                            dest,
                            addr,
                            size: 2,
                        });
                        dest
                    }
                    4 => {
                        self.il.push(Emil::Load {
                            dest,
                            addr,
                            size: 4,
                        });
                        dest
                    }
                    8 => {
                        self.il.push(Emil::Load {
                            dest,
                            addr,
                            size: 8,
                        });
                        dest
                    }
                    _ => {
                        unimplemented!("Unimplemented load size of {} bytes", l.size());
                    }
                }
            }
            ExprKind::BoolToInt(conv) => {
                let value = self.add_expr(&conv.operand(), ilr);
                let size: u8 = conv
                    .size()
                    .try_into()
                    .expect("Invalid bool conversion size");
                self.il.push(Emil::BoolToInt(value.next(), value, size));
                value.next()
            }
            ExprKind::Pop(p) => {
                let size: u8 = p.size().try_into().expect("Invalid pop size");
                self.il.push(Emil::Pop { size, dest: ilr });
                ilr
            }
            ExprKind::Add(a) | ExprKind::AddOverflow(a) => bin_op!(a, Add, self, ilr),
            ExprKind::And(a) => bin_op!(a, And, self, ilr),
            ExprKind::Asr(shift) => bin_op!(shift, Asr, self, ilr),
            ExprKind::Lsl(shift) => bin_op!(shift, Lsl, self, ilr),
            ExprKind::Lsr(shift) => bin_op!(shift, Lsr, self, ilr),
            ExprKind::Sub(s) => bin_op!(s, Sub, self, ilr),
            ExprKind::Mul(m) => bin_op!(m, Mul, self, ilr),
            ExprKind::Modu(mu) => bin_op!(mu, Modu, self, ilr),
            ExprKind::Divu(du) => bin_op!(du, Divu, self, ilr),
            ExprKind::Divs(ds) => bin_op!(ds, Divs, self, ilr),
            ExprKind::Or(or) => bin_op!(or, Or, self, ilr),
            ExprKind::Xor(xor) => bin_op!(xor, Xor, self, ilr),
            ExprKind::Mods(ms) => bin_op!(ms, Mods, self, ilr),
            ExprKind::CmpE(c) => bin_op!(c, CmpE, self, ilr),
            ExprKind::CmpNe(c) => bin_op!(c, CmpNe, self, ilr),
            ExprKind::CmpSlt(c) => bin_op!(c, CmpSlt, self, ilr),
            ExprKind::CmpUlt(c) => bin_op!(c, CmpUlt, self, ilr),
            ExprKind::CmpSle(c) => bin_op!(c, CmpSle, self, ilr),
            ExprKind::CmpUle(c) => bin_op!(c, CmpUle, self, ilr),
            ExprKind::CmpSge(c) => bin_op!(c, CmpSge, self, ilr),
            ExprKind::CmpUge(c) => bin_op!(c, CmpUge, self, ilr),
            ExprKind::CmpSgt(c) => bin_op!(c, CmpSgt, self, ilr),
            ExprKind::CmpUgt(c) => bin_op!(c, CmpUgt, self, ilr),
            ExprKind::Fmul(mul) => bin_op!(mul, Fmul, self, ilr),
            ExprKind::Fadd(add) => bin_op!(add, Fadd, self, ilr),
            ExprKind::Fsub(sub) => bin_op!(sub, Fsub, self, ilr),
            ExprKind::FcmpE(cmp) => bin_op!(cmp, FcmpE, self, ilr),
            ExprKind::FcmpNE(cmp) => bin_op!(cmp, FcmpNE, self, ilr),
            ExprKind::FcmpLT(cmp) => bin_op!(cmp, FcmpLT, self, ilr),
            ExprKind::FcmpLE(cmp) => bin_op!(cmp, FcmpLE, self, ilr),
            ExprKind::FcmpGE(cmp) => bin_op!(cmp, FcmpGE, self, ilr),
            ExprKind::FcmpGT(cmp) => bin_op!(cmp, FcmpGT, self, ilr),
            ExprKind::FcmpO(cmp) => bin_op!(cmp, FcmpO, self, ilr),
            ExprKind::FcmpUO(cmp) => bin_op!(cmp, FcmpUO, self, ilr),
            ExprKind::Sx(extend) => {
                let value = self.add_expr(&extend.operand(), ilr);
                let size: u8 = extend
                    .size()
                    .try_into()
                    .expect("Invalid sign extension size");
                self.il.push(Emil::SignExtend(value.next(), value, size));
                value.next()
            }
            ExprKind::Zx(extend) => {
                let value = self.add_expr(&extend.operand(), ilr);
                let size: u8 = extend
                    .size()
                    .try_into()
                    .expect("Invalid sign extension size");
                self.il.push(Emil::ZeroExtend(value.next(), value, size));
                value.next()
            }
            ExprKind::LowPart(lp) => {
                let value = self.add_expr(&lp.operand(), ilr);
                let size: u8 = lp.size().try_into().expect("Invalid size to truncate to");
                self.il.push(Emil::Truncate(value.next(), value, size));
                value.next()
            }
            ExprKind::Fneg(neg) => {
                let value = self.add_expr(&neg.operand(), ilr);
                self.il.push(Emil::Fneg(value.next(), value));
                value.next()
            }
            ExprKind::Fabs(abs) => {
                let value = self.add_expr(&abs.operand(), ilr);
                self.il.push(Emil::Fabs(value.next(), value));
                value.next()
            }
            ExprKind::FloatToInt(conv) => {
                let value = self.add_expr(&conv.operand(), ilr);
                let size = conv
                    .size()
                    .try_into()
                    .expect("Invalid floating point conversion size");
                self.il.push(Emil::FloatToInt(value.next(), value, size));
                value.next()
            }
            ExprKind::IntToFloat(conv) => {
                let value = self.add_expr(&conv.operand(), ilr);
                let size = conv
                    .size()
                    .try_into()
                    .expect("Invalid floating point conversion size");
                self.il.push(Emil::FloatToInt(value.next(), value, size));
                value.next()
            }
            ExprKind::Flag(_) => {
                self.il.push(Emil::Flag(ilr));
                ilr
            }
            _ => unimplemented!("Expression kind: {:?}", expr),
        }
    }
}
