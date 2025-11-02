use binaryninja::binary_view::{BinaryView, BinaryViewBase, BinaryViewExt};
use softmew::{MMU, Perm, page::Page};
use std::ops::Range;

use crate::{
    arch::{Endian, Intrinsic, RegState},
    prog::Program,
};

/// Load all of the sections of the binary into memory.
///
/// Just loads all of the sections that binary ninja knows of into virtual memory. Applies correct read and write
/// permissions to each section.
pub fn load_sections<P: Page>(memory: &mut MMU<P>, program: &BinaryView) -> Result<(), Range<u64>> {
    for segment in program.segments().iter() {
        let mut perm = Perm::NONE;
        let range = segment.address_range();
        if segment.readable() {
            perm |= Perm::READ;
        }
        if segment.writable() {
            perm |= Perm::WRITE;
        }
        let seg = memory
            .map_memory(
                range.start as usize,
                (range.end - range.start) as usize,
                perm,
            )
            .map_err(|_| range.clone())?;
        program.read(seg.as_mut(), range.start);
    }
    Ok(())
}

/// Load function at a specific address to the program.
///
/// Returns true if function was successfully added otherwise returns false.
pub fn load_function<P: Page, Regs: RegState, E: Endian, I: Intrinsic>(
    prog: &mut Program<P, Regs, E, I>,
    bv: &BinaryView,
    addr: u64,
) -> Result<(), &'static str> {
    if let Some(func) = bv.function_at(
        bv.default_platform()
            .expect("Should have default platform")
            .as_ref(),
        addr,
    ) {
        if let Ok(llil) = func.low_level_il() {
            prog.add_function(llil.as_ref());
            Ok(())
        } else {
            Err("No LLIL for function")
        }
    } else {
        Err("No function at address")
    }
}

/// Load all functions present in the binary view.
///
/// Returns the address of the first function that could not be loaded otherwise
/// just returns unit.
pub fn load_all_functions<P: Page, Regs: RegState, E: Endian, I: Intrinsic>(
    prog: &mut Program<P, Regs, E, I>,
    bv: &BinaryView,
) -> Result<(), String> {
    for func in bv.functions().iter() {
        load_function(prog, bv, func.start()).map_err(|e| format!("{:#x}: {e}", func.start()))?;
    }
    Ok(())
}
