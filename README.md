# Benchmark generation

This binary generates QF_FF SMT benchmarks that encode compilations of random
boolean formulae.

## Instructions

1. Install ZoKrates [link](https://zokrates.github.io/gettingstarted.html)
2. Clone this repository `git clone https://github.com/alex-ozdemir/ff-smt-bench-gen.git`
3. Clone the CirC repository `git clone https://github.com/circify/circ.git`
4. Run this binary with the `ZSHARP_STDLIB_PATH` set to a path to `third_party/ZoKrates/zokrates_stdlib` in the CirC clone.

Example run:

```zsh
export ZSHARP_STDLIB_PATH=PATH_WITH/third_party/ZoKrates/zokrates_stdlib/
cargo run -- --terms 5 --vars 3 -o xor --no-consts -t zokcirc --circ-opt
```

## Features

See the `--help` message for features.

* prime fields of variable bit-width (uses the first prime of that width, or
  BLS12-381's scalar field for width 255).
* configurable formula distribution
* configurable logic:
  * QF_FF
  * QF_NIA
  * QF_BV
  * Pure QF_FF (no boolean structure: just FF assertions)
