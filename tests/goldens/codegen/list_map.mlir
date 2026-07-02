// Atli tier-1 MLIR lowering. docs/calculus.md §9.1
// arena_slots = certified_beta + C = 1 + 0
module attributes {atli.certified_beta_slots = 1 : i64, atli.arena_overhead_slots = 0 : i64, atli.growable = false} {
  llvm.func @atli_entry_inc(i64) -> i64
  llvm.func @atli_entry_opt_value(i64) -> i64
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
  func.func private @atli_apply(%fn_id: i64, %arg: i64) -> i64
  func.func private @atli_scope_push(%label: i64, %mode: i64, %value: i64, %watermark: i64) -> ()
  func.func private @atli_scope_pop() -> ()
  func.func private @atli_scope_perform(%label: i64, %arg: i64) -> i64
  func.func @atli_beta_slots() -> i64 {
    %beta = arith.constant 1 : i64
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
  func.func @atli_fn_unwrap_or(%o: i64, %d: i64) -> i64 {
    %c0 = arith.constant 0 : i64
    %tag1 = func.call @atli_array_get(%o, %c0) : (i64, i64) -> i64
    %c2 = arith.constant 0 : i64
    %is_tag3 = arith.cmpi eq, %tag1, %c2 : i64
    %variant_case4 = scf.if %is_tag3 -> (i64) {
      scf.yield %d : i64
    } else {
      %c5 = arith.constant 1 : i64
      %payload6 = func.call @atli_array_get(%o, %c5) : (i64, i64) -> i64
      scf.yield %payload6 : i64
    }
    return %variant_case4 : i64
  }
  func.func @atli_fn_inc(%x: i64) -> i64 {
    %c0 = arith.constant 1 : i64
    %add1 = arith.addi %x, %c0 : i64
    return %add1 : i64
  }
  func.func @atli_fn_opt_value(%o: i64) -> i64 {
    %c0 = arith.constant 0 : i64
    %call1 = func.call @atli_fn_unwrap_or(%o, %c0) : (i64, i64) -> i64
    return %call1 : i64
  }
  func.func @atli_fn_map(%xs: i64, %f: i64) -> i64 {
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
      %apply16 = func.call @atli_apply(%f, %payload12) : (i64, i64) -> i64
      %call17 = func.call @atli_fn_map(%payload14, %f) : (i64, i64) -> i64
      %c18 = arith.constant 3 : i64
      %c19 = arith.constant 0 : i64
      %aggregate20 = func.call @atli_array_new(%c18, %c19) : (i64, i64) -> i64
      %c21 = arith.constant 0 : i64
      // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
      %aggregate_store22 = func.call @atli_array_inplace_set(%aggregate20, %c21, %c15) : (i64, i64, i64) -> i64
      %c23 = arith.constant 1 : i64
      // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
      %aggregate_store24 = func.call @atli_array_inplace_set(%aggregate20, %c23, %apply16) : (i64, i64, i64) -> i64
      %c25 = arith.constant 2 : i64
      // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
      %aggregate_store26 = func.call @atli_array_inplace_set(%aggregate20, %c25, %call17) : (i64, i64, i64) -> i64
      scf.yield %aggregate20 : i64
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
    %c28 = arith.constant 1 : i64
    %c29 = arith.constant 1 : i64
    %c30 = arith.constant 3 : i64
    %c31 = arith.constant 2 : i64
    %c32 = arith.constant 0 : i64
    %aggregate33 = func.call @atli_array_new(%c31, %c32) : (i64, i64) -> i64
    %c34 = arith.constant 0 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store35 = func.call @atli_array_inplace_set(%aggregate33, %c34, %c29) : (i64, i64, i64) -> i64
    %c36 = arith.constant 1 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store37 = func.call @atli_array_inplace_set(%aggregate33, %c36, %c30) : (i64, i64, i64) -> i64
    %c38 = arith.constant 0 : i64
    %c39 = arith.constant 3 : i64
    %c40 = arith.constant 0 : i64
    %aggregate41 = func.call @atli_array_new(%c39, %c40) : (i64, i64) -> i64
    %c42 = arith.constant 0 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store43 = func.call @atli_array_inplace_set(%aggregate41, %c42, %c38) : (i64, i64, i64) -> i64
    %c44 = arith.constant 3 : i64
    %c45 = arith.constant 0 : i64
    %aggregate46 = func.call @atli_array_new(%c44, %c45) : (i64, i64) -> i64
    %c47 = arith.constant 0 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store48 = func.call @atli_array_inplace_set(%aggregate46, %c47, %c28) : (i64, i64, i64) -> i64
    %c49 = arith.constant 1 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store50 = func.call @atli_array_inplace_set(%aggregate46, %c49, %aggregate33) : (i64, i64, i64) -> i64
    %c51 = arith.constant 2 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store52 = func.call @atli_array_inplace_set(%aggregate46, %c51, %aggregate41) : (i64, i64, i64) -> i64
    %c53 = arith.constant 3143532439223462023 : i64
    %call54 = func.call @atli_fn_map(%aggregate21, %c53) : (i64, i64) -> i64
    %c55 = arith.constant 5716541611359485172 : i64
    %call56 = func.call @atli_fn_map(%aggregate46, %c55) : (i64, i64) -> i64
    %call57 = func.call @atli_fn_sum(%call54) : (i64) -> i64
    %call58 = func.call @atli_fn_sum(%call56) : (i64) -> i64
    %add59 = arith.addi %call57, %call58 : i64
    return %add59 : i64
  }
  func.func @atli_program_main() -> i64 {
    %r = func.call @atli_fn_main() : () -> i64
    return %r : i64
  }
}
