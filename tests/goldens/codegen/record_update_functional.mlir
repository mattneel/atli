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
  func.func @atli_fn_main() -> i64 {
    %c0 = arith.constant 1 : i64
    %c1 = arith.constant 2 : i64
    %c2 = arith.constant 2 : i64
    %c3 = arith.constant 0 : i64
    %aggregate4 = func.call @atli_array_new(%c2, %c3) : (i64, i64) -> i64
    %c5 = arith.constant 0 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store6 = func.call @atli_array_inplace_set(%aggregate4, %c5, %c0) : (i64, i64, i64) -> i64
    %c7 = arith.constant 1 : i64
    // aggregate construction, calculus.md §9.2: one data allocation, field stores in place
    %aggregate_store8 = func.call @atli_array_inplace_set(%aggregate4, %c7, %c1) : (i64, i64, i64) -> i64
    %c9 = arith.constant 0 : i64
    %c10 = arith.constant 7 : i64
    // functional record update, calculus.md §5/§9.2: shallow copy allocation
    %record_update11 = func.call @atli_array_copy_set(%aggregate4, %c9, %c10) : (i64, i64, i64) -> i64
    %c12 = arith.constant 0 : i64
    %field13 = func.call @atli_array_get(%record_update11, %c12) : (i64, i64) -> i64
    return %field13 : i64
  }
  func.func @atli_program_main() -> i64 {
    %r = func.call @atli_fn_main() : () -> i64
    return %r : i64
  }
}
