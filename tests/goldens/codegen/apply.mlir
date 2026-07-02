// Atli tier-1 MLIR lowering. docs/calculus.md §9.1
// arena_slots = certified_beta + C = 0 + 0
module attributes {atli.certified_beta_slots = 0 : i64, atli.arena_overhead_slots = 0 : i64, atli.growable = false} {
  llvm.func @atli_entry_inc(i64) -> i64
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
    %beta = arith.constant 0 : i64
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
  func.func @atli_fn_inc(%x: i64) -> i64 {
    %c0 = arith.constant 1 : i64
    %add1 = arith.addi %x, %c0 : i64
    return %add1 : i64
  }
  func.func @atli_fn_apply(%f: i64, %x: i64) -> i64 {
    %apply0 = func.call @atli_apply(%f, %x) : (i64, i64) -> i64
    return %apply0 : i64
  }
  func.func @atli_fn_main() -> i64 {
    %c0 = arith.constant 3143532439223462023 : i64
    %c1 = arith.constant 5 : i64
    %call2 = func.call @atli_fn_apply(%c0, %c1) : (i64, i64) -> i64
    return %call2 : i64
  }
  func.func @atli_program_main() -> i64 {
    %r = func.call @atli_fn_main() : () -> i64
    return %r : i64
  }
}
