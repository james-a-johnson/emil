import argparse

import binaryninja as bn

NATIVE_SIZES: set[int] = set([1, 2, 4, 8])


def mask(size: int) -> int:
    hex = "ff" * size
    return int.from_bytes(bytes.fromhex(hex), "little")


def list_archs(_args):
    archs = bn.Architecture
    for arch in list(archs):
        print(arch)


def gen_reg_enum(arch, file):
    regs = arch.regs
    reg_type = f"{arch}Reg"
    file.write("#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]\n")
    file.write(f"pub enum {reg_type} {{\n")
    for k, _v in regs.items():
        file.write(f"    {k},\n")
    file.write("}\n\n")
    file.write(f"impl TryFrom<u32> for {reg_type} {{\n")
    file.write("\ttype Error = u32;\n\n")
    file.write("\tfn try_from(reg_id: u32) -> Result<Self, u32> {\n")
    file.write("\t\tmatch reg_id {\n")
    for k, v in regs.items():
        reg_id = v.index
        file.write(f"\t\t\t{reg_id} => Ok(Self::{k}),\n")
    file.write("\t\t\t_ => Err(reg_id),\n")
    file.write("\t\t}\n\t}\n}\n\n")
    file.write(f"impl std::fmt::Display for {reg_type} {{\n")
    file.write(
        "\tfn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {\n"
    )
    file.write('\t\twrite!(f, "{:?}", self)\n')
    file.write("\t}\n}\n\n")
    file.write(f"impl Register for {reg_type} {{}}\n\n")


def gen_read_reg(arch: bn.Architecture, name: str, info: bn.RegisterInfo) -> str:
    read = ""
    full_width = arch.regs[info.full_width_reg]
    if info.offset == 0 and info.size == full_width.size:
        match info.size:
            case 1:
                read += f"ILVal::Byte(self.{info.full_width_reg})\n"
            case 2:
                read += f"ILVal::Short(self.{info.full_width_reg})\n"
            case 4:
                read += f"ILVal::Word(self.{info.full_width_reg})\n"
            case 8:
                read += f"ILVal::Quad(self.{info.full_width_reg})\n"
            case _:
                read += f"ILVal::Big(Big::from(self.{info.full_width_reg}))\n"
    else:
        if full_width.size in NATIVE_SIZES:
            read += f"let val = self.{info.full_width_reg};\n"
            if info.offset != 0:
                read += f"let val = val >> (8 * {info.offset});\n"
            match info.size:
                case 1:
                    read += "ILVal::Byte(val as u8)\n"
                case 2:
                    read += "ILVal::Short(val as u16)\n"
                case 4:
                    read += "ILVal::Word(val as u32)\n"
                case 8:
                    read += "ILVal::Quad(val as u64)\n"
                case _:
                    read += (
                        f"ILVal::Big(Big::from(&val.to_le_bytes()[0..{info.size}))\n"
                    )
        else:
            # Working on a register that is just stored as an array of bytes. Need to just use indexes into it
            # to get the value out.
            offset = info.offset
            size = info.size
            start = offset
            end = offset + size
            match info.size:
                case 1:
                    read += f"ILVal::Byte(self.{info.full_width_reg}[{start}])\n"
                case 2:
                    read += f"let val = &self.{info.full_width_reg};\n"
                    read += f"ILVal::Short(u16::from_le_bytes([val[{start}], val[{start + 1}]]))\n"
                case 4:
                    read += f"let val = &self.{info.full_width_reg};\n"
                    read += f"ILVal::Word(u32::from_le_bytes([val[{start}], val[{start + 1}], val[{start + 2}], val[{start + 3}]]))\n"
                case 8:
                    read += f"let val = &self.{info.full_width_reg};\n"
                    read += f"ILVal::Quad(u64::from_le_bytes([val[{start}], val[{start + 1}], val[{start + 2}], val[{start + 3}], val[{start + 4}], val[{start + 5}], val[{start + 6}], val[{start + 7}]]))\n"
                case _:
                    read += f"let val = &self.{info.full_width_reg};\n"
                    read += f"ILVal::Big(Big::from(&val[{start}..{end}]))\n"

    return read


def gen_reg_file(arch: bn.Architecture, file):
    reg_file = f"{arch}RegFile"
    reg_id = f"{arch}Reg"
    regs = arch.regs
    # Binary Ninja's list of full width registers is not the most precise. Need to make our own list of all of the
    # expected full width registers.
    full_width = set()
    for reg in arch.full_width_regs:
        full_width.add(reg)
    for reg, info in arch.regs.items():
        if reg in full_width:
            continue
        if info.full_width_reg in full_width:
            continue
        full_width.add(info.full_width_reg)
    file.write("#[derive(Clone, Copy, Debug, Default)]\n")
    file.write(f"pub struct {reg_file} {{\n")
    for r in full_width:
        full_reg = regs[r]
        match full_reg.size:
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
    for reg, info in regs.items():
        file.write(f"\t\t\t{reg_id}::{reg} => {{\n")
        read = gen_read_reg(arch, reg, info)
        for line in read.split("\n"):
            if line == "":
                continue
            file.write(f"\t\t\t\t{line}\n")
        file.write("\t\t\t}\n")

    file.write("\t\t}\n")
    file.write("\t}\n\n")

    file.write(
        '\tfn write(&mut self, id: Self::RegID, val: &ILVal) { unimplemented!("Writing not supported yet") }\n'
    )
    file.write("}\n\n")


def gen_arch(args):
    arch = bn.Architecture[args.arch]
    file = args.outfile
    file.write(f"//! Register file definition for {arch}.\n//!\n")
    file.write("//! This file was generated by `gen_reg_file.py`\n\n")
    file.write("#![allow(non_camel_case_types)]\n\n")
    file.write("use crate::{Register, RegState};\n")
    file.write("use val::{Big, ILVal};\n\n")
    gen_reg_enum(arch, file)
    gen_reg_file(arch, file)


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
