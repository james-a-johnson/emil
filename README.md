# emil

Emulation of Binary Ninja's LLIL.

This project enables emulation of programs that have been analyzed in a
Binary Ninja database. This allows for emulating programs that you don't trust
to run on your host or don't match the architecture of your host environment.

Emil is done as a capstone project for the Master of Science in Cybersecurity
program at Georgia Institute of Technology.

Emil is currently a work in progress.

## Current Status
Currently the arm64 architecture has the best support. It has been tested and
some full programs have been emulated using it. The major problems with
supporting architectures right now (in theory) is just supporting all of the
architectural intrinsics that Binary Ninja defines.

There is also some support for rv64 as well. That is less tested but should work
if there are no intrinsics that get hit.

## Adding a New Architecture
1. Add support for all of the architecture registers
    - You can use the python script at `regs/gen_reg_file.py`
    - That script will automatically generate a struct that will handle register
      reads and writes for the architecture from the Binary Ninja architecture
      description
2. Add the architecture to `emulator/src/arch/[arch].rs`
    - Need to create a struct that implements the `State` trait
    - Will require the registers from the first step and creating an intrinsic
      enum or struct
    - Can add support for any intrinsics, syscalls, or other extra behavior you
      want
3. Initialize the state you created with required memory and then pass it to an
   emulator and start emulating

## Development Notes
**Make sure the binaryninja-api version matches the version you have installed**
