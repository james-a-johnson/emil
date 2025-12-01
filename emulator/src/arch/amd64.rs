use crate::arch::Intrinsic;
pub use regs::x86_64::{x86_64Reg as Amd64Reg, x86_64RegFile as Amd64State};

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
