"""
Script for comparing instruction traces between qemu and the emulator.

Get a trace from qemu by using `qemu-aarch64 -one-insn-per-tb -d nochain,cpu`
"""


ECHO_MAIN: int = 0x404678
QEMU_OFFSET: int = 0x000075445d843eb0 - 0x403eb0


qemu_addrs = []
with open("./qemu_echo.txt", "r") as fd:
    for line in fd:
        line = line.strip()
        if line == "":
            continue
        pc = line.split(" ")[0]
        pc, addr = pc.split("=")
        if pc != "PC":
            continue
        addr = int(addr, 16)
        qemu_addrs.append(addr - QEMU_OFFSET)


print(qemu_addrs[0:10])


emu_addrs = [0x403eb4]
with open("./emu_echo.txt", "r") as fd:
    for line in fd:
        line = line.strip()
        if line == "":
            continue
        pc = line.split("=")[1].strip()
        addr = int(pc[2:], 16)
        if addr == emu_addrs[-1]:
            continue
        emu_addrs.append(addr)


qemu_idx = qemu_addrs.index(ECHO_MAIN)
emu_idx = emu_addrs.index(ECHO_MAIN)

while True:
    if emu_addrs[emu_idx] != qemu_addrs[qemu_idx]:
        if emu_addrs[emu_idx] == qemu_addrs[qemu_idx + 1]:
            qemu_idx += 1
            continue
        print(f"{hex(emu_addrs[emu_idx])}\t{hex(qemu_addrs[qemu_idx])}")
        break
    emu_idx += 1
    qemu_idx += 1
