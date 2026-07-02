# Grades as codegen licenses

| Grade evidence | Backend license | Empirical v0.2.0 check |
| --- | --- | --- |
| finite β | allocate exactly β frame slots | compiled high-water ≤ β and corrupted-β trap |
| β = ω / Div | growable segment | `server_loop` bounded-run path |
| effect row | runtime handler-scope dispatch | oracle/native handler differentials |
| one-shot continuation use | omit release hot-path used flag | debug one-shot trap and wedge rejection |
| Q uniqueness | mutate unique arrays in place | oracle/native value equality; allocation counter drops |


Sprint 11 adds the first consumer of `Q`: a unique `^Array` binding has grade `1`, and the checker spends that single use to license native in-place stores. Functional `set` and `inplace set` are value-equivalent on accepted programs; the allocation counter is where the optimization becomes visible.


Sprint 14 spends the same `Q` idea parametrically: `^u` is a preservation variable. A helper can be polymorphic over ownership and still compile once under erasure, but it cannot mutate through `^u` because the shared instantiation would be unsound.
