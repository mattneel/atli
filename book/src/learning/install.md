# Install and run

Atli v0.2.0 is a research compiler with two execution paths: the oracle interpreter and native MLIR lowering. From a clone:

```sh
cargo build
cargo run -- run examples/fib.atli
```

The output is `55`.

The same program can compile and run natively:

```sh
cargo run -- run --compiled examples/fib.atli
```

Use `atli test examples/` to run every checked example through the documented directives.
