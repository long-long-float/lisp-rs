lisp-rs
=========

This is a lisp interpreter written in Rust, and implementing a subset of Scheme.

```shell
$ cargo run -r examples/mandelbrot.scm
```

To compile for RISC-V 32, use a option `-c`. 

The compiler outputs `out.bin` and `out.elf`. 
A file `out.bin` is raw instructions.
A file `out.elf` is instructions formatted by ELF.

Note that it is experimental, therefore the compiler fails or outputs invalid code.

```shell
$ cargo run -r -- -c source.scm
```

![mandelbrot](./examples/mandelbrot.png)

Run tests by

```
$ cargo test
```

# Milestones

- [x] Run FizzBuzz
- [x] Draw Mandelbrot set
- [x] Support statically type system with inference.
- [ ] Compiler for RISC-V
- [ ] Implement a lisp interpreter running in lisp-rs.

# Reference

* https://schemers.org/Documents/Standards/R5RS/HTML/
* https://cs61a.org/articles/scheme-spec/
