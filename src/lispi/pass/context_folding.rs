//!
//! This step has only memo and is not implemented.
//!
//! This step removes contextual arguments of closures.
//! For example, let's consider the following code.
//!
//! ```lisp
//! (define f (lambda () 42))
//! (define g (lambda () (f))
//! (g)
//! ```
//!
//! Note that functions `f` and `g` are defined at the root context, and function `g` don't know function `f`.
//! This code is compiled to,
//!
//! ```text
//! function f()() { ret 42 }
//!
//! function g()(ff) {
//!   %var = call %ff
//!   ret %var
//! }
//!
//! function main()() {
//!   call g, f
//! }
//! ```
//!
//! Function `g` takes an contextual argument `f` to know outer variables.
//! The value `f` is constant and can be folded in this step.
//!
//! ```text
//! function f()() { ret 42 }
//!
//! function g()() {
//!   %var = call f
//!   ret %var
//! }
//!
//! function main()() {
//!   call g
//! }
//! ```
//!
//! Now, values satisfying the following conditions are folded.
//!
//! 1. Value is a function label.
//! 2. All of values passed to functions are equaled.
//!
