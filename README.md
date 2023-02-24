# Plonk Draft

## Run
Since this Plonk does not implement a arithmetic circuit compiler, I added a self-defined circuit as an example. 

The circuit is:
```
x1 * x1 = x2
x3 * x3 = x4
x5 * x5 = x6
x2 + x4 = x6
```

To run the proof system, simple input following commands
```
cargo build
cargo run
```

## Further improvement
- Fiat-Shamir Transform
- NTT
- Arithmetic Circuit Compiler
- Lookup Table
- Custom Gates
- Different Commitment


## Source
This short demo is hugely relying on [Plonk paper](https://eprint.iacr.org/2019/953.pdf) and a Plonk analysis blog: [part1](https://research.metastate.dev/plonk-by-hand-part-1/), [part2](https://research.metastate.dev/plonk-by-hand-part-2-the-proof/), [part3](https://research.metastate.dev/plonk-by-hand-part-3-verification/)
