import argparse
from dataclasses import dataclass, field
from typing import Dict, List, Optional

import binaryninja as bn

NATIVE_SIZES: set[int] = set([1, 2, 4, 8])
"""Sizes of integers in bytes that host machines natively support"""


def map_reg_name(name: str) -> str:
    """Convert a register name to something that is valid for a rust field.

    Binary ninja may use a name for a register that is not a valid identifier in rust. This method will
    convert it to one that can be used as a rust field.
    """
    new_name = ""
    for c in name:
        match c:
            case ".":
                new_name += "_"
            case "[" | "]":
                continue
            case _:
                new_name += c
    return new_name


@dataclass
class Register:
    """A single register in an architecture.

    Holds all of the required information to represent the register in an emulator
    and parse it from binary ninja.
    """

    name: str = field(init=False)
    """Name of the register that should be used in the struct"""
    arch_name: str
    """Name used by Binary Ninja for the register"""
    size: int
    offset: int
    """Offset into the parent register if it has one. Otherwise just zero."""
    index: int
    """Index of the register as defined by Binary Ninja"""
    parent: Optional[str]

    def __post_init__(self):
        self.name = map_reg_name(self.arch_name)

    def __hash__(self) -> int:
        return self.arch_name.__hash__()

    def __str__(self) -> str:
        return self.name

    def __lt__(self, other) -> bool:
        return self.name < other.name

    @property
    def full_width(self) -> bool:
        return self.parent is None

    @staticmethod
    def from_bn_reg(name: str, info: bn.RegisterInfo) -> "Register":
        parent = info.full_width_reg if name != info.full_width_reg else None
        if info.index is None:
            raise ValueError(f"{name} has no index")
        return Register(name, info.size, info.offset, info.index, parent)


@dataclass
class Architecture:
    """All of the registers supported by an architecture."""

    name: str
    """Name of the architecture."""
    all_regs: Dict[str, Register]
    """All of the registers defined by the architecture."""
    full_size: List[Register]
    """List of the full size registers defined by the architecture."""
    little_endian: bool
    usize: int
    """Number of bytes required to address memory"""

    def __str__(self) -> str:
        return self.name

    def __getitem__(self, reg_name: str) -> Register:
        return self.all_regs[reg_name]

    @staticmethod
    def from_bn_arch(name: str, arch: bn.Architecture) -> "Architecture":
        all_regs = [
            Register.from_bn_reg(name, info) for name, info in arch.regs.items()
        ]
        greatest_index = max(map(lambda r: r.index, all_regs))
        # Add special register for emil to use as the program counter. Currently just used with the
        # gdb stub implementation.
        all_regs.append(
            Register("emil_pc", arch.address_size, 0, greatest_index + 1, None)
        )
        regs: Dict[str, Register] = {reg.name: reg for reg in all_regs}
        full_size = []
        for reg in regs.values():
            if reg.full_width:
                full_size.append(reg)
        return Architecture(
            name,
            regs,
            sorted(full_size),
            arch.endianness == bn.Endianness.LittleEndian,
            arch.address_size,
        )


def mask(size: int) -> int:
    hex = "ff" * size
    return int.from_bytes(bytes.fromhex(hex), "little")


def list_archs(_args):
    archs = bn.Architecture
    for arch in list(archs):
        print(arch)


def gen_reg_enum(arch: Architecture, file):
    """Define the enum that represents each register in the architecture."""
    reg_type = f"{arch}Reg"
    reg_names = list(arch.all_regs.keys())
    reg_names = sorted(reg_names)
    file.write("#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]\n")
    file.write(f"pub enum {reg_type} {{\n")
    for reg_name in reg_names:
        reg = arch.all_regs[reg_name]
        file.write(f"\t{reg.name},\n")
    file.write("}\n\n")
    file.write(f"impl TryFrom<u32> for {reg_type} {{\n")
    file.write("\ttype Error = u32;\n\n")
    file.write("\tfn try_from(reg_id: u32) -> Result<Self, u32> {\n")
    file.write("\t\tmatch reg_id {\n")
    for reg in arch.all_regs.values():
        file.write(f"\t\t\t{reg.index} => Ok(Self::{reg.name}),\n")
    file.write("\t\t\t_ => Err(reg_id),\n")
    file.write("\t\t}\n\t}\n}\n\n")
    file.write(f"impl std::fmt::Display for {reg_type} {{\n")
    file.write(
        "\tfn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {\n"
    )
    file.write('\t\twrite!(f, "{:?}", self)\n')
    file.write("\t}\n}\n\n")
    file.write(f"impl Register for {reg_type} {{\n")
    file.write("\tfn size(&self) -> u8 {\n")
    file.write("\t\tmatch self {\n")
    for reg in arch.all_regs.values():
        file.write(f"\t\t\tSelf::{reg.name} => {reg.size},\n")
    file.write("\t\t}\n\t}\n}\n\n")


def gen_read_reg(reg: Register, all: Dict[str, Register]) -> str:
    """Generate the case that will handle reading the specified register.

    Returns the code that handles reading the register. Returned code must be added to the register file
    struct.

    :param reg: Register to generate read code for
    :param all: Dictionary of all of the registers in the architecture
    :return: String of code to read register assuming that code is in the register file struct
    """
    read = ""
    if reg.full_width:
        match reg.size:
            case 1:
                read += f"ILVal::Byte(self.{reg.name})\n"
            case 2:
                read += f"ILVal::Short(self.{reg.name})\n"
            case 4:
                read += f"ILVal::Word(self.{reg.name})\n"
            case 8:
                read += f"ILVal::Quad(self.{reg.name})\n"
            case _:
                read += f"ILVal::Big(Big::from(self.{reg.name}))\n"
    else:
        assert reg.parent is not None, (
            "This case is checked by handling full width registers above"
        )
        full_width = all[reg.parent]
        if full_width.size in NATIVE_SIZES:
            read += f"let val = self.{full_width.name};\n"
            if reg.offset != 0:
                read += f"let val = val >> ({8 * reg.offset});\n"
            match reg.size:
                case 1:
                    read += "ILVal::Byte(val as u8)\n"
                case 2:
                    read += "ILVal::Short(val as u16)\n"
                case 4:
                    read += "ILVal::Word(val as u32)\n"
                case 8:
                    read += "ILVal::Quad(val as u64)\n"
                case _:
                    read += f"ILVal::Big(Big::from(&val.to_le_bytes()[0..{reg.size}))\n"
        else:
            # Working on a register that is just stored as an array of bytes. Need to just use indexes into it
            # to get the value out.
            offset = reg.offset
            size = reg.size
            start = offset
            end = offset + size
            match reg.size:
                case 1:
                    read += f"ILVal::Byte(self.{full_width.name}[{start}])\n"
                case 2:
                    read += f"let val = &self.{full_width.name};\n"
                    read += f"ILVal::Short(u16::from_le_bytes([val[{start}], val[{start + 1}]]))\n"
                case 4:
                    read += f"let val = &self.{full_width.name};\n"
                    read += f"ILVal::Word(u32::from_le_bytes([val[{start}], val[{start + 1}], val[{start + 2}], val[{start + 3}]]))\n"
                case 8:
                    read += f"let val = &self.{full_width.name};\n"
                    read += f"ILVal::Quad(u64::from_le_bytes([val[{start}], val[{start + 1}], val[{start + 2}], val[{start + 3}], val[{start + 4}], val[{start + 5}], val[{start + 6}], val[{start + 7}]]))\n"
                case _:
                    read += f"let val = &self.{full_width.name};\n"
                    read += f"ILVal::Big(Big::from(&val[{start}..{end}]))\n"

    return read


def gen_write_reg(reg: Register, all: Dict[str, Register]) -> str:
    """Generate code to write specified register.

    :param reg: Register to write value to
    :param all: Dictionary of all of the registers in the architecture
    :return: Code to add to register file struct
    """
    write = ""
    if reg.full_width:
        match reg.size:
            case 1:
                write += f"self.{reg.name} = val.get_byte();\n"
            case 2:
                write += f"self.{reg.name} = val.get_short();\n"
            case 4:
                write += f"self.{reg.name} = val.get_word();\n"
            case 8:
                write += f"self.{reg.name} = val.get_quad();\n"
            case _:
                write += "let big = val.get_big();\n"
                write += f'let arr: [u8; {reg.size}] = big.as_ref().try_into().expect("Value wrong size for {reg.name}");\n'
                write += f"self.{reg.name} = arr;\n"
    else:
        assert reg.parent is not None, (
            "This case is checked by handling full width registers above"
        )
        full_width = all[reg.parent]
        if full_width.size in NATIVE_SIZES:
            match reg.size:
                case 1:
                    mask = 0xFF << (reg.offset * 8)
                    write += "let val = val.get_byte();\n"
                    write += f"let val = (val as u{full_width.size * 8}) << ({8 * reg.offset});\n"
                    write += f"self.{full_width.name} &= !{mask};\n"
                    write += f"self.{full_width.name} |= val;\n"
                case 2:
                    mask = 0xFFFF << (reg.offset * 8)
                    write += "let val = val.get_short();\n"
                    write += f"let val = (val as u{full_width.size * 8}) << ({8 * reg.offset});\n"
                    write += f"self.{full_width.name} &= !{mask};\n"
                    write += f"self.{full_width.name} |= val;\n"
                case 4:
                    mask = 0xFFFFFFFF << (reg.offset * 8)
                    write += "let val = val.get_word();\n"
                    write += f"let val = (val as u{full_width.size * 8}) << ({8 * reg.offset});\n"
                    write += f"self.{full_width.name} &= !{mask};\n"
                    write += f"self.{full_width.name} |= val;\n"
                case 8:
                    mask = 0xFFFFFFFFFFFFFFFF << (reg.offset * 8)
                    write += "let val = val.get_quad();\n"
                    write += f"let val = (val as u{full_width.size * 8}) << ({8 * reg.offset});\n"
                    write += f"self.{full_width.name} &= !{mask};\n"
                    write += f"self.{full_width.name} |= val;\n"
                case _:
                    # In this case, treat the native sized register as just an array of bytes and then copy stuff in.
                    write += f"let bytes = unsafe {{ std::slice::from_raw_parts_mut(&mut self.{full_width.name} as *mut u8, {full_width.size * 8}) }};\n"
                    write += "let val = val.get_big();\n"
                    write += f"bytes[{reg.offset}..][..{reg.size}].copy_from_slice(val.as_ref())\n;"
        else:
            # Working on a register that is just stored as an array of bytes. Need to just use indexes into it
            # to set it.
            match reg.size:
                case 1:
                    write += f"self.{full_width.name}[{reg.offset}] = val.get_byte();\n"
                case 2:
                    write += "let val = val.get_short().to_le_bytes();\n"
                    write += f"self.{full_width.name}[{reg.offset}] = val[0];\n"
                    write += f"self.{full_width.name}[{reg.offset + 1}] = val[1];\n"
                case 4:
                    write += "let val = val.get_word().to_le_bytes();\n"
                    write += f"self.{full_width.name}[{reg.offset}] = val[0];\n"
                    write += f"self.{full_width.name}[{reg.offset + 1}] = val[1];\n"
                    write += f"self.{full_width.name}[{reg.offset + 2}] = val[2];\n"
                    write += f"self.{full_width.name}[{reg.offset + 3}] = val[3];\n"
                case 8:
                    write += "let val = val.get_quad().to_le_bytes();\n"
                    write += f"self.{full_width.name}[{reg.offset}] = val[0];\n"
                    write += f"self.{full_width.name}[{reg.offset + 1}] = val[1];\n"
                    write += f"self.{full_width.name}[{reg.offset + 2}] = val[2];\n"
                    write += f"self.{full_width.name}[{reg.offset + 3}] = val[3];\n"
                    write += f"self.{full_width.name}[{reg.offset + 4}] = val[4];\n"
                    write += f"self.{full_width.name}[{reg.offset + 5}] = val[5];\n"
                    write += f"self.{full_width.name}[{reg.offset + 6}] = val[6];\n"
                    write += f"self.{full_width.name}[{reg.offset + 7}] = val[7];\n"
                case _:
                    write += "let val = val.get_big();\n"
                    write += f"self.{full_width.name}[{reg.offset}..][..{reg.size}].copy_from_slice(val.as_ref());\n"
    return write


def gen_reg_file(arch: Architecture, file):
    """Add the register file struct to the file."""
    reg_file = f"{arch}RegFile"
    reg_id = f"{arch}Reg"
    # Binary Ninja's list of full width registers is not the most precise. Need to make our own list of all of the
    # expected full width registers.
    defaultable = all(map(lambda r: r.size <= 32, arch.full_size))
    if defaultable:
        file.write("#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]\n")
    else:
        file.write("#[derive(Clone, Copy, Debug, PartialEq, Eq)]\n")
    file.write(f"pub struct {reg_file} {{\n")
    for r in arch.full_size:
        match r.size:
            case 1:
                file.write(f"\tpub {r}: u8,\n")
            case 2:
                file.write(f"\tpub {r}: u16,\n")
            case 4:
                file.write(f"\tpub {r}: u32,\n")
            case 8:
                file.write(f"\tpub {r}: u64,\n")
            case s:
                file.write(f"\tpub {r}: [u8; {s}],\n")
    file.write("}\n\n")

    if not defaultable:
        file.write(
            f"impl Default for {reg_file} {{\n\tfn default() -> Self {{\n\t\tSelf {{\n"
        )
        for r in arch.full_size:
            match r.size:
                case 1 | 2 | 4 | 8:
                    file.write(f"\t\t\t{r}: 0,\n")
                case _:
                    file.write(f"\t\t\t{r}: [0u8; {r.size}],\n")
        file.write("\t\t}\n\t}\n}\n\n")

    file.write(f"impl RegState for {reg_file} {{\n")
    file.write(f"\ttype RegID = {reg_id};\n\n")
    file.write("\tfn read(&self, id: Self::RegID) -> ILVal {\n")
    file.write("\t\tmatch id {\n")
    for reg in arch.all_regs.values():
        file.write(f"\t\t\t{reg_id}::{reg.name} => {{\n")
        read = gen_read_reg(reg, arch.all_regs)
        for line in read.split("\n"):
            if line == "":
                continue
            file.write(f"\t\t\t\t{line}\n")
        file.write("\t\t\t}\n")

    file.write("\t\t}\n")
    file.write("\t}\n\n")

    file.write("\tfn write(&mut self, id: Self::RegID, val: &ILVal) {\n")
    file.write("\t\tmatch id {\n")
    for reg in arch.all_regs.values():
        file.write(f"\t\t\t{reg_id}::{reg.name} => {{\n")
        write = gen_write_reg(reg, arch.all_regs)
        for line in write.split("\n"):
            if line == "":
                continue
            file.write(f"\t\t\t\t{line}\n")
        file.write("\t\t\t}\n")
    file.write("\t\t}\n")
    file.write("\t}\n")

    file.write("}\n\n")


def gen_regid_trait(arch: Architecture) -> str:
    """Implement the RegId trait from gdbstub for the given architecture.

    Uses the gdb index as the id of the register.
    """
    impl = f"impl RegId for {arch}Reg {{\n"
    impl += "\tfn from_raw_id(id: usize) -> Option<(Self, Option<NonZeroUsize>)> {\n"
    impl += "\t\tlet reg_id: u32 = id.try_into().ok()?;\n"
    impl += f"\t\tlet reg: {arch}Reg = reg_id.try_into().ok()?;\n"
    impl += "\t\tlet size = NonZeroUsize::new(reg.size() as usize);\n"
    impl += "\t\tSome((reg, size))\n"
    impl += "\t}\n}"
    return impl


def gen_registers_trait(arch: Architecture) -> str:
    impl = ""
    impl += f"impl Registers for {arch}RegFile {{\n"
    match arch.usize:
        case 1:
            impl += "\ttype ProgramCounter = u8;\n\n"
        case 2:
            impl += "\ttype ProgramCounter = u16;\n\n"
        case 4:
            impl += "\ttype ProgramCounter = u32;\n\n"
        case 8:
            impl += "\ttype ProgramCounter = u64;\n\n"
        case _:
            raise ValueError("Don't support address size that is not a power of two")
    impl += "\tfn pc(&self) -> Self::ProgramCounter {\n"
    impl += "\t\tself.emil_pc\n\t}\n\n"
    impl += "\tfn gdb_serialize(&self, mut write_byte: impl FnMut(Option<u8>)) {\n"
    byte_method = "to_le_bytes" if arch.little_endian else "to_be_bytes"
    for reg in arch.full_size:
        if reg.size in NATIVE_SIZES:
            impl += f"\t\tself.{reg}.{byte_method}().iter().for_each(|b| write_byte(Some(*b)));\n"
        elif arch.little_endian:
            impl += f"\t\tself.{reg}.iter().for_each(|b| write_byte(Some(*b)));\n"
        else:
            impl += f"\t\tself.{reg}.iter().rev().for_each(|b| write_byte(Some(*b)));\n"

    impl += "\t}\n\n"

    impl += "\tfn gdb_deserialize(&mut self, bytes: &[u8]) -> Result<(), ()> {\n"
    total_size = sum(map(lambda r: r.size, arch.full_size))
    impl += f"\t\tif bytes.len() != {total_size} {{ return Err(()); }}\n"
    parse_method = "from_le_bytes" if arch.little_endian else "from_be_bytes"
    offset = 0
    for reg in arch.full_size:
        match reg.size:
            case 1:
                impl += f"\t\tself.{reg} = bytes[{offset}];\n"
            case 2:
                impl += f"\t\tself.{reg} = u16::{parse_method}(bytes[{offset}..][..2].try_into().unwrap());\n"
            case 4:
                impl += f"\t\tself.{reg} = u32::{parse_method}(bytes[{offset}..][..4].try_into().unwrap());\n"
            case 8:
                impl += f"\t\tself.{reg} = u64::{parse_method}(bytes[{offset}..][..8].try_into().unwrap());\n"
            case _:
                impl += f"\t\tself.{reg}.copy_from_slice(&bytes[{offset}..][..{reg.size}]);\n"
                if not arch.little_endian:
                    impl += f"\t\tself.{reg}.reverse();"
        offset += reg.size

    impl += "\t\tOk(())\n"
    impl += "\t}\n"
    impl += "}\n"
    return impl


def gen_gdb_info(arch: Architecture, file):
    """Add the gdb module to the architecture description.

    This will add all the required info for supporting the target using the gdbstub crate.
    """
    file.write("pub mod gdb {\n")
    file.write("\tuse super::*;\n")
    file.write("\tuse gdbstub::arch::{RegId, Registers};\n")
    file.write("\tuse std::num::NonZeroUsize;\n\n")
    reg_id_impl = gen_regid_trait(arch)
    for impl_line in reg_id_impl.splitlines():
        file.write(f"\t{impl_line}\n")
    file.write("\n")

    regs_impl = gen_registers_trait(arch)
    for impl_line in regs_impl.splitlines():
        file.write(f"\t{impl_line}\n")
    file.write("}\n")


def gen_arch(args):
    arch = bn.Architecture[args.arch]
    arch = Architecture.from_bn_arch(args.arch, arch)
    file = args.outfile
    file.write(f"//! Register file definition for {arch}.\n//!\n")
    file.write("//! This file was generated by `gen_reg_file.py`\n\n")
    file.write("#![allow(non_camel_case_types)]\n\n")
    file.write("use crate::{Register, RegState};\n")
    file.write("#[allow(unused_imports)]\n")
    file.write("use val::{Big, ILVal};\n\n")
    gen_reg_enum(arch, file)
    gen_reg_file(arch, file)
    gen_gdb_info(arch, file)


def main():
    args = argparse.ArgumentParser(
        description="Generate a register file for an architecture supported by binary ninja"
    )
    subparsers = args.add_subparsers(required=True)

    list = subparsers.add_parser("list", description="List supported architectures")
    list.set_defaults(func=list_archs)

    gen = subparsers.add_parser(
        "gen", description="Generate register file for a specific architecture"
    )
    gen.add_argument(
        "arch", help="Architecture to generate register file for", type=str
    )
    gen.add_argument(
        "outfile", help="File to write source to", type=argparse.FileType("w")
    )
    gen.set_defaults(func=gen_arch)

    args = args.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
