lisp-rs
=========

This is a lisp interpreter written in Rust, and implementing a subset of Scheme.

```shell
$ cargo run -r examples/mandelbrot.scm
```

![mandelbrot](./examples/mandelbrot.png)

Run tests by

```
$ cargo test
```

# Milestones

- [x] Run FizzBuzz
- [x] Draw Mandelbrot set
- [ ] Support statically type system with inference.
- [ ] Compiler for RISC-V
- [ ] Implement a lisp interpreter running in lisp-rs.

# Reference

* https://schemers.org/Documents/Standards/R5RS/HTML/
* https://cs61a.org/articles/scheme-spec/
