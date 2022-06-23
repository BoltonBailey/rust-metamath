# rust-metamath

A Metamath verifier written in rust, forked from jzw2's implementation.

## Running

Compile it with `cargo build --release`, the binary should be in `/target/release`

Change to the correct directory then do `path/to/binary name-of-mm-file.mm`

## Features/Goals

The main goal of this fork is to produce a `no_std` implementation of a Metamath checker in rust, for use with [RiscZero's](https://www.risczero.com/) [zkVM](https://github.com/risc0/risc0-rust-starter).

## TODOs

Currently, we have removed `std` except for the use of file I/O in `main.rs`.