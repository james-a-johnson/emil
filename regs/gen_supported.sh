#!/bin/bash

set -e

python3 ./gen_reg_file.py gen x86_64 ./src/x86_64.rs
python3 ./gen_reg_file.py gen x86 ./src/x86.rs
python3 ./gen_reg_file.py gen aarch64 ./src/aarch64.rs
python3 ./gen_reg_file.py gen rv64gc ./src/rv64gc.rs
