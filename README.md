lisp-rs
=========

This is a lisp interpreter written in Rust.

```shell
$ cargo run -r examples/mandelbrot.scm
```

![mandelbrot](./examples/mandelbrot.png)

Run tests by

```
$ cargo test
```

It has following features.

- Basic form and functions (define, if, +, -...)
- Macros
- Statically typed with type inference
- Human readable errors (like rustc)
- REPL
- Optimizing tail recursion
- Generate code for RISC-V (WIP)

# Milestones

- [x] Run FizzBuzz
- [x] Draw Mandelbrot set
- [x] Support statically type system with inference.
- [ ] Compiler for RISC-V
- [ ] Implement a lisp interpreter running in lisp-rs.

# Reference

* https://schemers.org/Documents/Standards/R5RS/HTML/
* https://cs61a.org/articles/scheme-spec/
