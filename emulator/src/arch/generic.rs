use crate::arch::{Endian, RegState};
use crate::emil::ILVal;
use std::rc::Rc;
use std::{collections::HashMap, marker::PhantomData};

use std::ops::{Index, IndexMut};

use binaryninja::architecture::{Architecture, CoreArchitecture, Register, RegisterInfo};

#[derive(Clone, Copy, Debug)]
pub struct RegId(u32);

impl std::fmt::Display for RegId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Register({})", self.0)
    }
}

impl std::convert::TryFrom<u32> for RegId {
    type Error = ();
    fn try_from(value: u32) -> Result<Self, Self::Error> {
        Ok(Self(value))
    }
}

impl crate::arch::Register for RegId {
    fn id(&self) -> u32 {
        self.0
    }
}

#[derive(Clone, Copy, Debug)]
struct RegInfo {
    offset: usize,
    size: usize,
}

pub struct GenericRegs<E> {
    /// All of the registers as a flat array of bytes.
    ///
    /// Register accesses will just access some number of contiguous bytes in this array.
    data: Vec<u8>,
    /// Mapping of a register id to the offset and number of bytes in the `data` field.
    regs: HashMap<u32, Rc<RegInfo>>,
    /// Mapping of register name to offset and number of bytes in the `data` field.
    reg_name: HashMap<String, Rc<RegInfo>>,
    /// Register ID to use as the syscall return register.
    syscall_id: u32,
    _e: PhantomData<E>,
}

impl<E: Endian> GenericRegs<E> {
    pub fn parse_from_arch(arch: &CoreArchitecture, sys_ret_id: u32) -> Self {
        let mut data = Vec::new();
        let mut map = HashMap::new();
        let mut names = HashMap::new();
        let full_regs = arch.registers_full_width();
        for reg in full_regs {
            let start = data.len();
            let size = reg.info().size();
            let info = Rc::new(RegInfo {
                offset: start,
                size,
            });
            data.resize(start + size, 0);
            map.insert(reg.id().0, Rc::clone(&info));
            names.insert(reg.name().into_owned(), info);
        }

        for reg in arch.registers_all() {
            let id = reg.id().0;
            if map.contains_key(&id) {
                continue;
            }

            // At this point, the register must be a child of a full sized register. So it must have a parent.
            let parent = reg
                .info()
                .parent()
                .expect("This register must have a parent")
                .id()
                .0;
            let info = map.get(&parent).expect("Parent register must exist in map");
            let offset = info.offset + reg.info().offset();
            let size = reg.info().size();
            let info = Rc::new(RegInfo { offset, size });
            map.insert(id, Rc::clone(&info));
            names.insert(reg.name().into_owned(), info);
        }

        Self {
            data,
            regs: map,
            syscall_id: sys_ret_id,
            reg_name: names,
            _e: PhantomData,
        }
    }

    pub fn read_reg(&self, id: RegId) -> ILVal {
        let info = self.regs.get(&id.0).expect("Invalid register id");
        let offset = info.offset;
        let size = info.size;
        match size {
            1 => ILVal::Byte(self.data[offset]),
            _ => E::read(&self.data[offset..][..size]),
        }
    }

    pub fn write_reg(&mut self, id: RegId, val: ILVal) {
        let info = self.regs.get(&id.0).expect("Invalid register id");
        let offset = info.offset;
        let size = info.size;
        E::write(val, &mut self.data[offset..][..size]);
    }
}

impl<E> Index<&str> for GenericRegs<E> {
    type Output = [u8];

    /// Get the bytes of a specific register in native endianness.
    fn index(&self, index: &str) -> &Self::Output {
        let info = self.reg_name.get(index).expect("Invalid register name");
        &self.data[info.offset..][..info.size]
    }
}

impl<E> IndexMut<&str> for GenericRegs<E> {
    fn index_mut(&mut self, index: &str) -> &mut Self::Output {
        let info = self.reg_name.get(index).expect("Invalid register name");
        &mut self.data[info.offset..][..info.size]
    }
}

impl<E: Endian> RegState for GenericRegs<E> {
    type RegID = RegId;

    fn read(&self, id: Self::RegID) -> ILVal {
        todo!();
    }

    fn write(&mut self, id: Self::RegID, val: ILVal) {
        todo!();
    }

    fn set_syscall_return(&mut self, val: ILVal) {
        todo!();
    }
}
