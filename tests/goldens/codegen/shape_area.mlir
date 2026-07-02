// Atli tier-1 MLIR lowering. docs/calculus.md §9.1
// arena_slots = certified_beta + C = 0 + 0
module attributes {atli.certified_beta_slots = 0 : i64, atli.arena_overhead_slots = 0 : i64, atli.growable = false} {
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
  func.func private @atli_task_spawned() -> ()
  func.func private @atli_tick() -> ()
  func.func private @atli_scope_push(%label: i64, %mode: i64, %value: i64, %watermark: i64) -> ()
  func.func private @atli_scope_pop() -> ()
  func.func private @atli_scope_perform(%label: i64, %arg: i64) -> i64
  func.func @atli_beta_slots() -> i64 {
    %beta = arith.constant 0 : i64
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
    %beta = arith.constant 0 : i64
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
  func.func @atli_fn_area(%s: i64) -> i64 {
    %c0 = arith.constant 0 : i64
    %tag1 = func.call @atli_array_get(%s, %c0) : (i64, i64) -> i64
    %c2 = arith.constant 0 : i64
    %is_tag3 = arith.cmpi eq, %tag1, %c2 : i64
    %variant_case4 = scf.if %is_tag3 -> (i64) {
      %c5 = arith.constant 1 : i64
      %payload6 = func.call @atli_array_get(%s, %c5) : (i64, i64) -> i64
      %c7 = arith.constant 3 : i64
      %mul8 = arith.muli %c7, %payload6 : i64
      %mul9 = arith.muli %mul8, %payload6 : i64
      scf.yield %mul9 : i64
    } else {
      %c10 = arith.constant 1 : i64
      %payload11 = func.call @atli_array_get(%s, %c10) : (i64, i64) -> i64
      %c12 = arith.constant 2 : i64
      %payload13 = func.call @atli_array_get(%s, %c12) : (i64, i64) -> i64
      %mul14 = arith.muli %payload11, %payload13 : i64
      scf.yield %mul14 : i64
    }
    return %variant_case4 : i64
  }
  func.func @atli_fn_main() -> i64 {
    %c0 = arith.constant 1 : i64
    %c1 = arith.constant 3 : i64
    %c2 = arith.constant 4 : i64
    %c3 = arith.constant 3 : i64
    %c4 = arith.constant 0 : i64
    %aggregate5 = func.call @atli_array_new(%c3, %c4) : (i64, i64) -> i64
    %c6 = arith.constant 0 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store7 = func.call @atli_array_inplace_set(%aggregate5, %c6, %c0) : (i64, i64, i64) -> i64
    %c8 = arith.constant 1 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store9 = func.call @atli_array_inplace_set(%aggregate5, %c8, %c1) : (i64, i64, i64) -> i64
    %c10 = arith.constant 2 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store11 = func.call @atli_array_inplace_set(%aggregate5, %c10, %c2) : (i64, i64, i64) -> i64
    %call12 = func.call @atli_fn_area(%aggregate5) : (i64) -> i64
    return %call12 : i64
  }
  func.func @atli_program_main() -> i64 {
    %r = func.call @atli_fn_main() : () -> i64
    return %r : i64
  }
}
