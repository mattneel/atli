# CLI and test directives

`atli test <dir>` reads top-of-file comment directives:

```text
// expect: 55
// expect-oracle: text
// expect-compiled: text
// expect-check-error: substring
// env: KEY=VALUE
```

Each `.atli` file under `examples/` carries one of these headers, so CI checks every Book tutorial include through both paths where applicable.
