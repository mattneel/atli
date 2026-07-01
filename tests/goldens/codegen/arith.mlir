// Atli tier-1 textual MLIR artifact. docs/calculus.md §9.1
// arena_slots = certified_beta + C = 0 + 0
module attributes {atli.certified_beta_slots = 0 : i64, atli.arena_overhead_slots = 0 : i64} {
func.func @main() -> i64 attributes {atli.high_water_slot_claim = 0 : i64} {
%result = arith.constant 14 : i64
return %result : i64
}
}
