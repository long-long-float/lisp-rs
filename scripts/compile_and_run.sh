#!/bin/sh

# To enable debug output, change `-i` to `-d`.
cargo run -- -c \
    -i tokens \
    -i ast \
    -i preprocessed-ast \
    -i type \
    -i optimized-ast \
    -i raw-ir \
    -i translate-cmp \
    -i remove-ref-and-deref \
    -i place-on-memory \
    -i remove-redundant-assignments \
    -i constant-folding \
    -i immediate-unfolding \
    -i remove-uncalled-functions \
    -i remove-phi-nodes \
    -i register-allocation \
    $1 && ./rv32emu/build/rv32emu out.elf