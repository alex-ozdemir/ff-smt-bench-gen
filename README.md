# Benchmark generation

This binary generates QF_FF SMT benchmarks that encode compilations of random
boolean formulae.

Example run:

```zsh
export ZSHARP_STDLIB_PATH=PATH_WITH/zokrates_stdlib/
cargo run -- --terms 5 --vars 3 -o xor --no-consts -t zokcirc --circ-opt
```

## Features

* prime fields of variable bit-width (uses the first prime of that width, or
  BLS12-381's scalar field for width 255).
* configurable formula distribution
* configurable logic:
  * QF_FF
  * QF_NIA
  * QF_BV
  * Pure QF_FF (no boolean structure: just FF assertions)

## Notes

* ZoKrates:
  * to use the ZoKrates toolchain (`-t zokref`) you must install ZoKrates on
    your system
  * to use CirC's zokrates compiler (`-t zokcirc`), you'll need to set the
    `ZSHARP_STDLIB_PATH` variable

