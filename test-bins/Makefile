all: hello-riscv sum-stdin

.PHONY: clean


clean:
	rm -f *.o
	rm -f hello-riscv
	rm -f sum-stdin


# This binary just prints hello world to standard out and then exits.
# Very simple binary for testing if things are initially working.
hello-riscv: hello-riscv.asm
	riscv64-linux-gnu-as --noexecstack -fPIC -march=rv64gc -mlittle-endian -o hello-riscv.o hello-riscv.asm
	riscv64-linux-gnu-ld --no-dynamic-linker -EL -s -o hello-riscv hello-riscv.o


# Reads whitespace delimited numbers from standard in, sums them up, and prints
# the sum to standard out. This is a full C program that statically links libc
# so it requires a lot of emulation support to be able to run the entire thing.
sum-stdin: sum-stdin.c
	riscv64-linux-gnu-gcc-12 -march=rv64imdc -mlittle-endian -static -Og -o sum-stdin sum-stdin.c
