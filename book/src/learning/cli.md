# Mutual recursion and the CLI

Mutually recursive top-level declarations elaborate to `fix*` groups:

```zig
{{#include ../../../examples/even_odd.atli:3:}}
```

Useful commands:

- `atli check file.atli`
- `atli run file.atli`
- `atli run --compiled file.atli`
- `atli core file.atli`
- `atli emit file.atli`
- `atli build file.atli`
- `atli test examples/`
- `atli --version`
