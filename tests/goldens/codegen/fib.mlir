// Atli tier-1 MLIR lowering. docs/calculus.md §9.1
// arena_slots = certified_beta + C = 2 + 0
module attributes {atli.certified_beta_slots = 2 : i64, atli.arena_overhead_slots = 0 : i64} {
  memref.global "private" @atli_high_water : memref<1xi64> = dense<0>
  func.func private @atli_trap_overflow() -> ()
  func.func private @atli_trap_one_shot() -> ()
  func.func @atli_beta_slots() -> i64 {
    %beta = arith.constant 2 : i64
    return %beta : i64
  }
  func.func @atli_high_water_value() -> i64 {
    %g = memref.get_global @atli_high_water : memref<1xi64>
    %c0 = arith.constant 0 : index
    %v = memref.load %g[%c0] : memref<1xi64>
    return %v : i64
  }
  func.func @atli_touch_frame(%slots: i64) -> () {
    %beta = arith.constant 2 : i64
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
  func.func @atli_fn_fib(%n: i64) -> i64 {
    %frame = arith.constant 1 : i64
    func.call @atli_touch_frame(%frame) : (i64) -> ()
    %c0 = arith.constant 0 : i64
    %is_zero1 = arith.cmpi eq, %n, %c0 : i64
    %case2 = scf.if %is_zero1 -> (i64) {
      %c3 = arith.constant 0 : i64
      scf.yield %c3 : i64
    } else {
      %c4 = arith.constant 1 : i64
      %pred5 = arith.subi %n, %c4 : i64
      %c6 = arith.constant 0 : i64
      %is_zero7 = arith.cmpi eq, %pred5, %c6 : i64
      %case8 = scf.if %is_zero7 -> (i64) {
        %c9 = arith.constant 1 : i64
        scf.yield %c9 : i64
      } else {
        %c10 = arith.constant 1 : i64
        %pred11 = arith.subi %pred5, %c10 : i64
        %call12 = func.call @atli_fn_fib(%pred5) : (i64) -> i64
        %c13 = arith.constant 1 : i64
        %gt14 = arith.cmpi sgt, %pred5, %c13 : i64
        %monus15 = scf.if %gt14 -> (i64) {
          %diff16 = arith.subi %pred5, %c13 : i64
          scf.yield %diff16 : i64
        } else {
          %zero17 = arith.constant 0 : i64
          scf.yield %zero17 : i64
        }
        %call18 = func.call @atli_fn_fib(%monus15) : (i64) -> i64
        %add19 = arith.addi %call12, %call18 : i64
        scf.yield %add19 : i64
      }
      scf.yield %case8 : i64
    }
    return %case2 : i64
  }
  func.func @atli_fn_main() -> i64 {
    %c0 = arith.constant 10 : i64
    %call1 = func.call @atli_fn_fib(%c0) : (i64) -> i64
    return %call1 : i64
  }
  func.func @atli_program_main() -> i64 {
    %r = func.call @atli_fn_main() : () -> i64
    return %r : i64
  }
}
