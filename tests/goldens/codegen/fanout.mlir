// Atli tier-1 MLIR lowering. docs/calculus.md §9.1
// arena_slots = certified_beta + C = 0 + 0
module attributes {atli.certified_beta_slots = 0 : i64, atli.arena_overhead_slots = 0 : i64, atli.growable = false} {
  llvm.func @atli_entry_work(i64) -> i64
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
  func.func @atli_fn_work(%n: i64) -> i64 {
    %c0 = arith.constant 1 : i64
    %add1 = arith.addi %n, %c0 : i64
    return %add1 : i64
  }
  func.func @atli_fn_main() -> i64 {
    // scope, calculus.md §9.3: enter task group and join children on exit
    func.call @atli_scope_enter() : () -> ()
    %c0 = arith.constant 1 : i64
    %c1 = arith.constant 0 : i64
    %c2 = arith.constant 0 : i64
    %task_fn3 = llvm.mlir.addressof @atli_entry_work : !llvm.ptr
    // spawn, calculus.md §9.3: child arena sized from callee CertifiedGrade
    %task4 = func.call @atli_spawn(%task_fn3, %c0, %c1, %c2) : (!llvm.ptr, i64, i64, i64) -> i64
    %c5 = arith.constant 2 : i64
    %c6 = arith.constant 0 : i64
    %c7 = arith.constant 0 : i64
    %task_fn8 = llvm.mlir.addressof @atli_entry_work : !llvm.ptr
    // spawn, calculus.md §9.3: child arena sized from callee CertifiedGrade
    %task9 = func.call @atli_spawn(%task_fn8, %c5, %c6, %c7) : (!llvm.ptr, i64, i64, i64) -> i64
    %c10 = arith.constant 3 : i64
    %c11 = arith.constant 0 : i64
    %c12 = arith.constant 0 : i64
    %task_fn13 = llvm.mlir.addressof @atli_entry_work : !llvm.ptr
    // spawn, calculus.md §9.3: child arena sized from callee CertifiedGrade
    %task14 = func.call @atli_spawn(%task_fn13, %c10, %c11, %c12) : (!llvm.ptr, i64, i64, i64) -> i64
    %await15 = func.call @atli_await(%task4) : (i64) -> i64
    %await16 = func.call @atli_await(%task9) : (i64) -> i64
    %add17 = arith.addi %await15, %await16 : i64
    %await18 = func.call @atli_await(%task14) : (i64) -> i64
    %add19 = arith.addi %add17, %await18 : i64
    func.call @atli_scope_exit() : () -> ()
    return %add19 : i64
  }
  func.func @atli_program_main() -> i64 {
    %r = func.call @atli_fn_main() : () -> i64
    return %r : i64
  }
}
