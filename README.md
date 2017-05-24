# 4th-year-project
Github repository for my 4th year project code

Requires the Haskell Tool Stack and the Rust toolchain Cargo
Run stack setup && stack build in the compiler directory to build compiler
Run cargo build in the vm directory to build the vm
Example files in /tests; files without suffix are inputs, for convention I have used '.occ' as a suffix for compiled code.
Compile using 'cd tests; stack exec compiler-exe write <input-file> <output-file>'

Run files using
  cargo run -- -m <memory-size> -p <input-file>

Runs about 2750 LOC for compiler and 1850 LOC for virtual machine
