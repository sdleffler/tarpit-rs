# tarpit-rs: Smallfuck implemented in Rust's type system

This is a proof of the Turing-completeness of Rust's type system; it's an
implementation of [Smallfuck](https://esolangs.org/wiki/Smallfuck), a known
Turing complete language. Since Rust's type system may have a Turing-complete
language embedded in it, we know therefore it must be Turing-complete itself!
Neat.

Contained in this repository are both the type-level implementation *and* a
minimal, unoptimized runtime implementation for verifying the type-level
implementation. Additional tests can be added via the `sf_test!{}` macro, and
run using `cargo test`.