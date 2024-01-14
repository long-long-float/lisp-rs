#!/bin/sh

cargo run -- -c \
    -i tokens \
    -i ast \
    $1 && ./rv32emu/build/rv32emu out.elf