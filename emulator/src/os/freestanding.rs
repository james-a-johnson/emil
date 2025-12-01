use std::marker::PhantomData;

use softmew::{MMU, page::SimplePage};

use crate::arch::{
    Little, State,
    amd64::{Amd64Intrin, Amd64State},
};

const TEMP_BIT: u32 = 1 << 31;
const TEMP_MASK: u32 = !TEMP_BIT;

pub struct Freestanding<E, R, I> {
    regs: R,
    memory: MMU<SimplePage>,
    flags: [u64; 4],
    temp_flags: [u64; 4],
    _intrinsics: PhantomData<I>,
    _endianness: PhantomData<E>,
}

impl<E, R, I> Freestanding<E, R, I> {
    fn flag(&self, id: u32) -> bool {
        let temp = (id & TEMP_MASK) != 0;
        let id = id & TEMP_MASK;
        let index = id >> 6;
        let bit = id & 0b111111;
        if temp {
            ((self.temp_flags[index as usize] >> bit) & 1) == 1
        } else {
            ((self.flags[index as usize] >> bit) & 1) == 1
        }
    }

    fn flag_write(&mut self, value: bool, id: u32) {
        let temp = (id & TEMP_MASK) != 0;
        let id = id & TEMP_MASK;
        let index = id >> 6;
        let bit = id & 0b111111;
        if temp {
            let mut val = self.temp_flags[index as usize];
            val &= !(1 << bit);
            val |= (value as u64) << bit;
            self.temp_flags[index as usize] = val;
        } else {
            let mut val = self.flags[index as usize];
            val &= !(1 << bit);
            val |= (value as u64) << bit;
            self.flags[index as usize] = val;
        }
    }
}

impl State<SimplePage> for Freestanding<Little, Amd64State, Amd64Intrin> {
    type Endianness = Little;
    type Intrin = Amd64Intrin;
    type Registers = Amd64State;

    fn regs(&mut self) -> &mut Self::Registers {
        &mut self.regs
    }

    fn mem(&mut self) -> &mut MMU<SimplePage> {
        &mut self.memory
    }

    fn underlying(&mut self) -> (&mut Self::Registers, &mut MMU<SimplePage>) {
        (&mut self.regs, &mut self.memory)
    }

    fn syscall(&mut self, _addr: u64) -> crate::arch::SyscallResult {
        crate::arch::SyscallResult::Panic("Freestanding does not support system calls".into())
    }

    #[inline]
    fn get_flag(&self, id: u32) -> bool {
        self.flag(id)
    }

    fn set_flag(&mut self, val: bool, id: u32) {
        self.flag_write(val, id);
    }

    fn push(&mut self, val: &[u8]) -> Result<(), softmew::fault::Fault> {
        let mut sp = self.regs.rsp as usize;
        sp -= val.len();
        self.regs.rsp = sp as u64;
        self.memory.write_perm(sp, val)
    }

    fn pop(&mut self, data: &mut [u8]) -> Result<(), softmew::fault::Fault> {
        let sp = self.regs.rsp as usize;
        let updated_sp = sp - data.len();
        self.regs.rsp = updated_sp as u64;
        self.memory.read_perm(sp, data)
    }

    fn save_ret_addr(&mut self, addr: u64) -> Result<(), softmew::fault::Fault> {
        self.push(&addr.to_le_bytes())
    }

    fn intrinsic(&mut self, _intrin: &Self::Intrin) -> Result<(), softmew::fault::Fault> {
        panic!("Not implemented yet");
    }
}
