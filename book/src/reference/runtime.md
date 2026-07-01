# Runtime contracts

Native execution reports `ATLI_HIGH_WATER=<n> ATLI_BETA=<m>` on stderr. Trap exit 86 means certified arena overflow. Trap exit 87 means a debug one-shot violation. `ATLI_MAX_ITERS` bounds the growable `div` path in tests. `ATLI_FORCE_DYNAMIC_DISPATCH=1` disables lexical handler fast paths and forces the runtime handler-scope stack.
