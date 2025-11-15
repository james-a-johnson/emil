use crate::arch::{Big, Endian, Little, RegState};
use crate::emil::ILVal;
use std::collections::HashMap;
use std::rc::Rc;

use std::ops::{Index, IndexMut};

use binaryninja::Endianness;
use binaryninja::architecture::{Architecture, CoreArchitecture, Register, RegisterInfo};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

pub struct GenericRegs {
    /// All of the registers as a flat array of bytes.
    ///
    /// Register accesses will just access some number of contiguous bytes in this array.
    data: Vec<u8>,
    /// Mapping of a register id to the offset and number of bytes in the `data` field.
    regs: HashMap<u32, Rc<RegInfo>>,
    /// Mapping of register name to offset and number of bytes in the `data` field.
    reg_name: HashMap<String, Rc<RegInfo>>,
    /// Function to read bytes in either little or bit endian format.
    read_endian: fn(data: &[u8]) -> ILVal,
    /// Function to write data with the correct endianness.
    write_endian: fn(value: ILVal, data: &mut [u8]),
}

impl GenericRegs {
    pub fn parse_from_arch(arch: &CoreArchitecture) -> Self {
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

        if arch.endianness() == Endianness::LittleEndian {
            Self {
                data,
                regs: map,
                reg_name: names,
                read_endian: Little::read,
                write_endian: Little::write,
            }
        } else {
            Self {
                data,
                regs: map,
                reg_name: names,
                read_endian: Big::read,
                write_endian: Big::write,
            }
        }
    }

    pub fn reg_names(&self) -> impl Iterator<Item = &String> {
        self.reg_name.keys()
    }
}

impl From<&CoreArchitecture> for GenericRegs {
    fn from(value: &CoreArchitecture) -> Self {
        Self::parse_from_arch(value)
    }
}

impl Index<&str> for GenericRegs {
    type Output = [u8];

    /// Get the bytes of a specific register in host endian format.
    fn index(&self, index: &str) -> &Self::Output {
        let info = self.reg_name.get(index).expect("Invalid register name");
        &self.data[info.offset..][..info.size]
    }
}

impl IndexMut<&str> for GenericRegs {
    fn index_mut(&mut self, index: &str) -> &mut Self::Output {
        let info = self.reg_name.get(index).expect("Invalid register name");
        &mut self.data[info.offset..][..info.size]
    }
}

impl RegState for GenericRegs {
    type RegID = RegId;

    fn read(&self, id: Self::RegID) -> ILVal {
        let reg_info = self.regs.get(&id.0).expect("Invalid register id");
        let data = &self.data[reg_info.offset..][..reg_info.size];
        (self.read_endian)(data)
    }

    fn write(&mut self, id: Self::RegID, val: ILVal) {
        let reg_info = self.regs.get(&id.0).expect("Invalid register id");
        let data = &mut self.data[reg_info.offset..][..reg_info.size];
        (self.write_endian)(val, data);
    }
}
