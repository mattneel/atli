// Atli tier-1 MLIR lowering. docs/calculus.md §9.1
// arena_slots = certified_beta + C = 1 + 0
module attributes {atli.certified_beta_slots = 1 : i64, atli.arena_overhead_slots = 0 : i64, atli.growable = false} {
  memref.global "private" @atli_high_water : memref<1xi64> = dense<0>
  func.func private @atli_trap_overflow() -> ()
  func.func private @atli_trap_one_shot() -> ()
  func.func private @atli_trap_bounds() -> ()
  func.func private @atli_array_new(%len: i64, %fill: i64) -> i64
  func.func private @atli_array_get(%handle: i64, %idx: i64) -> i64
  func.func private @atli_array_copy_set(%handle: i64, %idx: i64, %value: i64) -> i64
  func.func private @atli_array_inplace_set(%handle: i64, %idx: i64, %value: i64) -> i64
  func.func private @atli_array_len(%handle: i64) -> i64
  func.func private @atli_data_allocs() -> i64
  func.func private @atli_tick() -> ()
  func.func private @atli_scope_push(%label: i64, %mode: i64, %value: i64, %watermark: i64) -> ()
  func.func private @atli_scope_pop() -> ()
  func.func private @atli_scope_perform(%label: i64, %arg: i64) -> i64
  func.func @atli_beta_slots() -> i64 {
    %beta = arith.constant 1 : i64
    return %beta : i64
  }
  func.func @atli_high_water_value() -> i64 {
    %g = memref.get_global @atli_high_water : memref<1xi64>
    %c0 = arith.constant 0 : index
    %v = memref.load %g[%c0] : memref<1xi64>
    return %v : i64
  }
  func.func @atli_debug_resume_once(%uses: i64) -> () {
    %one = arith.constant 1 : i64
    %bad = arith.cmpi sgt, %uses, %one : i64
    scf.if %bad {
      func.call @atli_trap_one_shot() : () -> ()
    }
    return
  }
  func.func @atli_touch_frame(%slots: i64) -> () {
    %beta = arith.constant 1 : i64
    %over = arith.cmpi sgt, %slots, %beta : i64
    scf.if %over {
      func.call @atli_trap_overflow() : () -> ()
    }
    %g = memref.get_global @atli_high_water : memref<1xi64>
    %c0 = arith.constant 0 : index
    %old = memref.load %g[%c0] : memref<1xi64>
    %gt = arith.cmpi sgt, %slots, %old : i64
    scf.if %gt {
      memref.store %slots, %g[%c0] : memref<1xi64>
    }
    return
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
    %c4 = arith.constant 1 : i64
    %c5 = arith.constant 3 : i64
    %c6 = arith.constant 0 : i64
    %c7 = arith.constant 3 : i64
    %c8 = arith.constant 0 : i64
    %aggregate9 = func.call @atli_array_new(%c7, %c8) : (i64, i64) -> i64
    %c10 = arith.constant 0 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store11 = func.call @atli_array_inplace_set(%aggregate9, %c10, %c6) : (i64, i64, i64) -> i64
    %c12 = arith.constant 3 : i64
    %c13 = arith.constant 0 : i64
    %aggregate14 = func.call @atli_array_new(%c12, %c13) : (i64, i64) -> i64
    %c15 = arith.constant 0 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store16 = func.call @atli_array_inplace_set(%aggregate14, %c15, %c4) : (i64, i64, i64) -> i64
    %c17 = arith.constant 1 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store18 = func.call @atli_array_inplace_set(%aggregate14, %c17, %c5) : (i64, i64, i64) -> i64
    %c19 = arith.constant 2 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store20 = func.call @atli_array_inplace_set(%aggregate14, %c19, %aggregate9) : (i64, i64, i64) -> i64
    %c21 = arith.constant 3 : i64
    %c22 = arith.constant 0 : i64
    %aggregate23 = func.call @atli_array_new(%c21, %c22) : (i64, i64) -> i64
    %c24 = arith.constant 0 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store25 = func.call @atli_array_inplace_set(%aggregate23, %c24, %c2) : (i64, i64, i64) -> i64
    %c26 = arith.constant 1 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store27 = func.call @atli_array_inplace_set(%aggregate23, %c26, %c3) : (i64, i64, i64) -> i64
    %c28 = arith.constant 2 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store29 = func.call @atli_array_inplace_set(%aggregate23, %c28, %aggregate14) : (i64, i64, i64) -> i64
    %c30 = arith.constant 3 : i64
    %c31 = arith.constant 0 : i64
    %aggregate32 = func.call @atli_array_new(%c30, %c31) : (i64, i64) -> i64
    %c33 = arith.constant 0 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store34 = func.call @atli_array_inplace_set(%aggregate32, %c33, %c0) : (i64, i64, i64) -> i64
    %c35 = arith.constant 1 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store36 = func.call @atli_array_inplace_set(%aggregate32, %c35, %c1) : (i64, i64, i64) -> i64
    %c37 = arith.constant 2 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store38 = func.call @atli_array_inplace_set(%aggregate32, %c37, %aggregate23) : (i64, i64, i64) -> i64
    %call39 = func.call @atli_fn_sum(%aggregate32) : (i64) -> i64
    return %call39 : i64
  }
  func.func @atli_program_main() -> i64 {
    %r = func.call @atli_fn_main() : () -> i64
    return %r : i64
  }
}
