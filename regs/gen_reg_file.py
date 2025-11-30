import argparse
from dataclasses import dataclass, field
from typing import Dict, Optional

import binaryninja as bn

NATIVE_SIZES: set[int] = set([1, 2, 4, 8])


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
    name: str = field(init=False)
    """Name of the register that should be used in the struct"""
    arch_name: str
    """Name used by Binary Ninja for the register"""
    size: int
    offset: int
    index: int
    """Index of the register as defined by Binary Ninja"""
    parent: Optional[str]

    def __post_init__(self):
        self.name = map_reg_name(self.arch_name)

    def __hash__(self) -> int:
        return self.arch_name.__hash__()

    def __str__(self) -> str:
        return self.name

    @property
    def full_width(self) -> bool:
        return self.parent is None

    @staticmethod
    def from_bn_reg(name: str, info: bn.RegisterInfo) -> "Register":
        parent = info.full_width_reg if name != info.full_width_reg else None
        if info.index is None:
            raise ValueError(f"{name} has no index")
        return Register(name, info.size, info.offset, info.index, parent)


def mask(size: int) -> int:
    hex = "ff" * size
    return int.from_bytes(bytes.fromhex(hex), "little")


def list_archs(_args):
    archs = bn.Architecture
    for arch in list(archs):
        print(arch)


def gen_reg_enum(arch: bn.Architecture, regs: Dict[str, Register], file):
    reg_type = f"{arch}Reg"
    file.write("#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]\n")
    file.write(f"pub enum {reg_type} {{\n")
    for reg in regs.values():
        file.write(f"\t{reg.name},\n")
    file.write("}\n\n")
    file.write(f"impl TryFrom<u32> for {reg_type} {{\n")
    file.write("\ttype Error = u32;\n\n")
    file.write("\tfn try_from(reg_id: u32) -> Result<Self, u32> {\n")
    file.write("\t\tmatch reg_id {\n")
    for reg in regs.values():
        file.write(f"\t\t\t{reg.index} => Ok(Self::{reg.name}),\n")
    file.write("\t\t\t_ => Err(reg_id),\n")
    file.write("\t\t}\n\t}\n}\n\n")
    file.write(f"impl std::fmt::Display for {reg_type} {{\n")
    file.write(
        "\tfn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {\n"
    )
    file.write('\t\twrite!(f, "{:?}", self)\n')
    file.write("\t}\n}\n\n")
    file.write(f"impl Register for {reg_type} {{}}\n\n")


def gen_read_reg(reg: Register, all: Dict[str, Register]) -> str:
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


def gen_reg_file(arch: bn.Architecture, regs: Dict[str, Register], file):
    reg_file = f"{arch}RegFile"
    reg_id = f"{arch}Reg"
    # Binary Ninja's list of full width registers is not the most precise. Need to make our own list of all of the
    # expected full width registers.
    full_width = set()
    for reg in regs.values():
        if reg.full_width:
            full_width.add(reg)
    file.write("#[derive(Clone, Copy, Debug, Default)]\n")
    file.write(f"pub struct {reg_file} {{\n")
    for r in full_width:
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

    file.write(f"impl RegState for {reg_file} {{\n")
    file.write(f"\ttype RegID = {reg_id};\n\n")
    file.write("\tfn read(&self, id: Self::RegID) -> ILVal {\n")
    file.write("\t\tmatch id {\n")
    for reg in regs.values():
        file.write(f"\t\t\t{reg_id}::{reg.name} => {{\n")
        read = gen_read_reg(reg, regs)
        for line in read.split("\n"):
            if line == "":
                continue
            file.write(f"\t\t\t\t{line}\n")
        file.write("\t\t\t}\n")

    file.write("\t\t}\n")
    file.write("\t}\n\n")

    file.write("\tfn write(&mut self, id: Self::RegID, val: &ILVal) {\n")
    file.write("\t\tmatch id {\n")
    for reg in regs.values():
        file.write(f"\t\t\t{reg_id}::{reg.name} => {{\n")
        write = gen_write_reg(reg, regs)
        for line in write.split("\n"):
            if line == "":
                continue
            file.write(f"\t\t\t\t{line}\n")
        file.write("\t\t\t}\n")
    file.write("\t\t}")
    file.write("\t}")

    file.write("}\n\n")


def gen_arch(args):
    arch = bn.Architecture[args.arch]
    all_regs = [Register.from_bn_reg(name, info) for name, info in arch.regs.items()]
    regs: Dict[str, Register] = {reg.name: reg for reg in all_regs}
    file = args.outfile
    file.write(f"//! Register file definition for {arch}.\n//!\n")
    file.write("//! This file was generated by `gen_reg_file.py`\n\n")
    file.write("#![allow(non_camel_case_types)]\n\n")
    file.write("use crate::{Register, RegState};\n")
    file.write("use val::{Big, ILVal};\n\n")
    gen_reg_enum(arch, regs, file)
    gen_reg_file(arch, regs, file)


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
