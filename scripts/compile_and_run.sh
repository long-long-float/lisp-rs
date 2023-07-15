#!/bin/sh

cargo run -- -cd $1 && ./rv32emu/build/rv32emu out.elf