# Runtime contracts

Native execution reports `ATLI_HIGH_WATER=<n> ATLI_BETA=<m> ATLI_DATA_ALLOCS=<k>` on stderr. Trap exit 86 means certified arena overflow. Trap exit 87 means a debug one-shot violation. Trap exit 88 means `ATLI BOUNDS` for array bounds or runtime scope bounds. `ATLI_DATA_ALLOCS` counts data-region array creations/copies; accepted `inplace set` sites do not increment it. `ATLI_MAX_ITERS` bounds the growable `div` path in tests. `ATLI_FORCE_DYNAMIC_DISPATCH=1` disables lexical handler fast paths and forces the runtime handler-scope stack.


## v0.3.0 structured data

Records and variants are implemented in v0.3.0. Normative syntax and lowering remain in `docs/syntax.md`, `docs/elaboration.md`, and `docs/calculus.md`; this Book chapter links the live examples rather than restating the rules.
