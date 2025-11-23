use std::ops::{Deref, DerefMut};

use crate::arch::generic::{GenericRegs, RegId};
use crate::arch::{Intrinsic, RegState};

use binaryninja::architecture::CoreArchitecture;

/// Wrapper around [`GenericRegs`] that contains the amd64 registers.
pub struct Amd64Regs(GenericRegs);

impl Amd64Regs {
    pub fn new() -> Self {
        let arch = CoreArchitecture::by_name("x86_64").expect("Binary Ninja supports amd64");
        Self(GenericRegs::parse_from_arch(&arch))
    }
}

impl Deref for Amd64Regs {
    type Target = GenericRegs;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Amd64Regs {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl RegState for Amd64Regs {
    type RegID = RegId;

    fn read(&self, id: Self::RegID) -> crate::emil::ILVal {
        self.0.read(id)
    }

    fn write(&mut self, id: Self::RegID, val: crate::emil::ILVal) {
        self.0.write(id, val);
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Amd64Intrin {
    Blank,
}

impl Intrinsic for Amd64Intrin {
    fn parse(
        _intrinsic: &binaryninja::low_level_il::operation::Operation<
            '_,
            binaryninja::low_level_il::function::Finalized,
            binaryninja::low_level_il::function::NonSSA,
            binaryninja::low_level_il::operation::Intrinsic,
        >,
    ) -> Result<Self, String> {
        Ok(Self::Blank)
    }
}
