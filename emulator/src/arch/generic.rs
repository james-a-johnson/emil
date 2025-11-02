use crate::arch::Endian;
use crate::emil::ILVal;
use std::{collections::HashMap, marker::PhantomData};

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
    regs: HashMap<u32, RegInfo>,
    /// Register ID to use as the syscall return register.
    syscall_id: u32,
    _e: PhantomData<E>,
}

impl<E: Endian> GenericRegs<E> {
    pub fn parse_from_arch(arch: &CoreArchitecture, sys_ret_id: u32) -> Self {
        let mut data = Vec::new();
        let mut map = HashMap::new();
        let full_regs = arch.registers_full_width();
        for reg in full_regs {
            let start = data.len();
            let size = reg.info().size();
            data.resize(start + size, 0);
            map.insert(
                reg.id().0,
                RegInfo {
                    offset: start,
                    size,
                },
            );
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
            let info = *map.get(&parent).expect("Parent register must exist in map");
            let offset = info.offset + reg.info().offset();
            let size = reg.info().size();
            map.insert(id, RegInfo { offset, size });
        }

        Self {
            data,
            regs: map,
            syscall_id: sys_ret_id,
            _e: PhantomData,
        }
    }

    pub fn read_reg(&self, id: RegId) -> ILVal {
        let RegInfo { offset, size } = *self.regs.get(&id.0).expect("Invalid register id");
        match size {
            1 => ILVal::Byte(self.data[offset]),
            _ => E::read(&self.data[offset..][..size]),
        }
    }

    pub fn write_reg(&mut self, id: RegId, val: ILVal) {
        let RegInfo { offset, size } = *self.regs.get(&id.0).expect("Invalid register id");
        E::write(val, &mut self.data[offset..][..size]);
    }
}
