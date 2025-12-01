# Register Files
This crate is for defining the register files for architectures that binary ninja supports.

Right now, none of the register files should be implemented manually. `gen_reg_file.py` can be used to automatically
generate the register file from the information provided by Binary Ninja. Run `gen_reg_file.py --help` to see the
exact usage. As an example, the arm64 register file was generated via `gen_reg_file.py gen aarch64 src/aarch64.rs`.
