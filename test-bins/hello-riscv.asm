.data         # declare and initialize variables
hello:  .asciz "Hello world!\n" # string with null terminator

  .text         # code starts here
  .globl _start
_start:           # label marking the entry point of the program
  addi a0, zero, 1
  la a1, hello  # load the address of hello into $a0 (1st argument)
  addi a2, zero, 13
  addi a7, zero, 0x40     # code to print the string at the address a0
  ecall         # make the system call

  addi a7, zero, 0x5d    # code to exit
  ecall         # make the system call
