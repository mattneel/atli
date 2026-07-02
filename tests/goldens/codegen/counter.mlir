// Atli tier-1 MLIR lowering. docs/calculus.md §9.1
// arena_slots = certified_beta + C = 1 + 0
module attributes {atli.certified_beta_slots = 1 : i64, atli.arena_overhead_slots = 0 : i64, atli.growable = false} {
  llvm.func @atli_entry_counter(i64) -> i64
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
  func.func @atli_fn_counter(%n: i64) -> i64 {
    %frame = arith.constant 1 : i64
    func.call @atli_touch_frame(%frame) : (i64) -> ()
    // handler-scope push, calculus.md §5: runtime innermost label search
    %c0 = arith.constant 4953246919537031357 : i64
    %c1 = arith.constant 2 : i64
    %c2 = arith.constant 1 : i64
    %scope_watermark3 = func.call @atli_high_water_value() : () -> i64
    func.call @atli_scope_push(%c0, %c1, %c2, %scope_watermark3) : (i64, i64, i64, i64) -> ()
    %c4 = arith.constant 0 : i64
    %is_zero5 = arith.cmpi eq, %n, %c4 : i64
    %hcase6 = scf.if %is_zero5 -> (i64) {
      %c7 = arith.constant 0 : i64
      scf.yield %c7 : i64
    } else {
      %c8 = arith.constant 1 : i64
      %pred9 = arith.subi %n, %c8 : i64
      %call10 = func.call @atli_fn_counter(%pred9) : (i64) -> i64
      // H-op-resume, calculus.md §5; static dispatch licensed by L5_mentions_iff_resume
      %c11 = arith.constant 1 : i64
      %add12 = arith.addi %call10, %c11 : i64
      %resume_uses13 = arith.constant 1 : i64
      func.call @atli_debug_resume_once(%resume_uses13) : (i64) -> ()
      scf.yield %add12 : i64
    }
    func.call @atli_scope_pop() : () -> ()
    return %hcase6 : i64
  }
  func.func @atli_fn_main() -> i64 {
    %c0 = arith.constant 3 : i64
    %call1 = func.call @atli_fn_counter(%c0) : (i64) -> i64
    return %call1 : i64
  }
  func.func @atli_program_main() -> i64 {
    %r = func.call @atli_fn_main() : () -> i64
    return %r : i64
  }
}
