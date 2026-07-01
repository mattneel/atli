# Witnesses, β, and high-water

`atli check` prints the certified witness: type, effect row, β, and divergence classification. β is the frame-slot allocation license. Native programs report high-water usage on stderr, and every compiled differential checks `high-water ≤ β`.

For divergent programs, β is `ω` and the growable segment path is used:

```zig
{{#include ../../../examples/server_loop.atli:5:}}
```
