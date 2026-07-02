// Atli tier-1 MLIR lowering. docs/calculus.md §9.1
// arena_slots = certified_beta + C = 2 + 0
module attributes {atli.certified_beta_slots = 2 : i64, atli.arena_overhead_slots = 0 : i64, atli.growable = false} {
  llvm.func @atli_entry_map(i64) -> i64
  llvm.func @atli_entry_sum(i64) -> i64
  func.func private @atli_trap_overflow() -> ()
  func.func private @atli_trap_one_shot() -> ()
  func.func private @atli_trap_bounds() -> ()
  func.func private @atli_touch_frame(%slots: i64) -> ()
  func.func private @atli_high_water_value() -> i64
  func.func private @atli_array_new(%len: i64, %fill: i64) -> i64
  func.func private @atli_array_get(%handle: i64, %idx: i64) -> i64
  func.func private @atli_array_copy_set(%handle: i64, %idx: i64, %value: i64) -> i64
  func.func private @atli_array_inplace_set(%handle: i64, %idx: i64, %value: i64) -> i64
  func.func private @atli_array_len(%handle: i64) -> i64
  func.func private @atli_data_allocs() -> i64
  func.func private @atli_spawn(%fn: !llvm.ptr, %arg: i64, %beta: i64, %growable: i64) -> i64
  func.func private @atli_await(%handle: i64) -> i64
  func.func private @atli_scope_enter() -> ()
  func.func private @atli_scope_exit() -> ()
  func.func private @atli_tick() -> ()
  func.func private @atli_scope_push(%label: i64, %mode: i64, %value: i64, %watermark: i64) -> ()
  func.func private @atli_scope_pop() -> ()
  func.func private @atli_scope_perform(%label: i64, %arg: i64) -> i64
  func.func @atli_beta_slots() -> i64 {
    %beta = arith.constant 2 : i64
    return %beta : i64
  }
  func.func @atli_debug_resume_once(%uses: i64) -> () {
    %one = arith.constant 1 : i64
    %bad = arith.cmpi sgt, %uses, %one : i64
    scf.if %bad {
      func.call @atli_trap_one_shot() : () -> ()
    }
    return
  }
  func.func @atli_fn_map(%xs: i64) -> i64 {
    %frame = arith.constant 1 : i64
    func.call @atli_touch_frame(%frame) : (i64) -> ()
    %c0 = arith.constant 0 : i64
    %tag1 = func.call @atli_array_get(%xs, %c0) : (i64, i64) -> i64
    %c2 = arith.constant 0 : i64
    %is_tag3 = arith.cmpi eq, %tag1, %c2 : i64
    %variant_case4 = scf.if %is_tag3 -> (i64) {
      %c5 = arith.constant 0 : i64
      %c6 = arith.constant 3 : i64
      %c7 = arith.constant 0 : i64
      %aggregate8 = func.call @atli_array_new(%c6, %c7) : (i64, i64) -> i64
      %c9 = arith.constant 0 : i64
      // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
      %aggregate_store10 = func.call @atli_array_inplace_set(%aggregate8, %c9, %c5) : (i64, i64, i64) -> i64
      scf.yield %aggregate8 : i64
    } else {
      %c11 = arith.constant 1 : i64
      %payload12 = func.call @atli_array_get(%xs, %c11) : (i64, i64) -> i64
      %c13 = arith.constant 2 : i64
      %payload14 = func.call @atli_array_get(%xs, %c13) : (i64, i64) -> i64
      %c15 = arith.constant 1 : i64
      %call16 = func.call @atli_fn_map(%payload14) : (i64) -> i64
      %c17 = arith.constant 3 : i64
      %c18 = arith.constant 0 : i64
      %aggregate19 = func.call @atli_array_new(%c17, %c18) : (i64, i64) -> i64
      %c20 = arith.constant 0 : i64
      // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
      %aggregate_store21 = func.call @atli_array_inplace_set(%aggregate19, %c20, %c15) : (i64, i64, i64) -> i64
      %c22 = arith.constant 1 : i64
      // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
      %aggregate_store23 = func.call @atli_array_inplace_set(%aggregate19, %c22, %payload12) : (i64, i64, i64) -> i64
      %c24 = arith.constant 2 : i64
      // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
      %aggregate_store25 = func.call @atli_array_inplace_set(%aggregate19, %c24, %call16) : (i64, i64, i64) -> i64
      scf.yield %aggregate19 : i64
    }
    return %variant_case4 : i64
  }
  func.func @atli_fn_sum(%xs: i64) -> i64 {
    %frame = arith.constant 1 : i64
    func.call @atli_touch_frame(%frame) : (i64) -> ()
    %c0 = arith.constant 0 : i64
    %tag1 = func.call @atli_array_get(%xs, %c0) : (i64, i64) -> i64
    %c2 = arith.constant 0 : i64
    %is_tag3 = arith.cmpi eq, %tag1, %c2 : i64
    %variant_case4 = scf.if %is_tag3 -> (i64) {
      %c5 = arith.constant 0 : i64
      scf.yield %c5 : i64
    } else {
      %c6 = arith.constant 1 : i64
      %payload7 = func.call @atli_array_get(%xs, %c6) : (i64, i64) -> i64
      %c8 = arith.constant 2 : i64
      %payload9 = func.call @atli_array_get(%xs, %c8) : (i64, i64) -> i64
      %call10 = func.call @atli_fn_sum(%payload9) : (i64) -> i64
      %add11 = arith.addi %payload7, %call10 : i64
      scf.yield %add11 : i64
    }
    return %variant_case4 : i64
  }
  func.func @atli_fn_main() -> i64 {
    %c0 = arith.constant 1 : i64
    %c1 = arith.constant 1 : i64
    %c2 = arith.constant 1 : i64
    %c3 = arith.constant 2 : i64
    %c4 = arith.constant 0 : i64
    %c5 = arith.constant 3 : i64
    %c6 = arith.constant 0 : i64
    %aggregate7 = func.call @atli_array_new(%c5, %c6) : (i64, i64) -> i64
    %c8 = arith.constant 0 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store9 = func.call @atli_array_inplace_set(%aggregate7, %c8, %c4) : (i64, i64, i64) -> i64
    %c10 = arith.constant 3 : i64
    %c11 = arith.constant 0 : i64
    %aggregate12 = func.call @atli_array_new(%c10, %c11) : (i64, i64) -> i64
    %c13 = arith.constant 0 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store14 = func.call @atli_array_inplace_set(%aggregate12, %c13, %c2) : (i64, i64, i64) -> i64
    %c15 = arith.constant 1 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store16 = func.call @atli_array_inplace_set(%aggregate12, %c15, %c3) : (i64, i64, i64) -> i64
    %c17 = arith.constant 2 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store18 = func.call @atli_array_inplace_set(%aggregate12, %c17, %aggregate7) : (i64, i64, i64) -> i64
    %c19 = arith.constant 3 : i64
    %c20 = arith.constant 0 : i64
    %aggregate21 = func.call @atli_array_new(%c19, %c20) : (i64, i64) -> i64
    %c22 = arith.constant 0 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store23 = func.call @atli_array_inplace_set(%aggregate21, %c22, %c0) : (i64, i64, i64) -> i64
    %c24 = arith.constant 1 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store25 = func.call @atli_array_inplace_set(%aggregate21, %c24, %c1) : (i64, i64, i64) -> i64
    %c26 = arith.constant 2 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store27 = func.call @atli_array_inplace_set(%aggregate21, %c26, %aggregate12) : (i64, i64, i64) -> i64
    %call28 = func.call @atli_fn_map(%aggregate21) : (i64) -> i64
    %c29 = arith.constant 1 : i64
    %c30 = arith.constant 1 : i64
    %c31 = arith.constant 3 : i64
    %c32 = arith.constant 2 : i64
    %c33 = arith.constant 0 : i64
    %aggregate34 = func.call @atli_array_new(%c32, %c33) : (i64, i64) -> i64
    %c35 = arith.constant 0 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store36 = func.call @atli_array_inplace_set(%aggregate34, %c35, %c30) : (i64, i64, i64) -> i64
    %c37 = arith.constant 1 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store38 = func.call @atli_array_inplace_set(%aggregate34, %c37, %c31) : (i64, i64, i64) -> i64
    %c39 = arith.constant 0 : i64
    %c40 = arith.constant 3 : i64
    %c41 = arith.constant 0 : i64
    %aggregate42 = func.call @atli_array_new(%c40, %c41) : (i64, i64) -> i64
    %c43 = arith.constant 0 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store44 = func.call @atli_array_inplace_set(%aggregate42, %c43, %c39) : (i64, i64, i64) -> i64
    %c45 = arith.constant 3 : i64
    %c46 = arith.constant 0 : i64
    %aggregate47 = func.call @atli_array_new(%c45, %c46) : (i64, i64) -> i64
    %c48 = arith.constant 0 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store49 = func.call @atli_array_inplace_set(%aggregate47, %c48, %c29) : (i64, i64, i64) -> i64
    %c50 = arith.constant 1 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store51 = func.call @atli_array_inplace_set(%aggregate47, %c50, %aggregate34) : (i64, i64, i64) -> i64
    %c52 = arith.constant 2 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store53 = func.call @atli_array_inplace_set(%aggregate47, %c52, %aggregate42) : (i64, i64, i64) -> i64
    %call54 = func.call @atli_fn_map(%aggregate47) : (i64) -> i64
    %call55 = func.call @atli_fn_sum(%call28) : (i64) -> i64
    %c56 = arith.constant 3 : i64
    %add57 = arith.addi %call55, %c56 : i64
    return %add57 : i64
  }
  func.func @atli_program_main() -> i64 {
    %r = func.call @atli_fn_main() : () -> i64
    return %r : i64
  }
}
