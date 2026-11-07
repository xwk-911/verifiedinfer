import Ptx.ISA.Shift

namespace Ptx.ShiftTests
open Ptx.ISA

def registers : RegisterDeclarations := [("wide",.u64),("bits",.b64),("word",.u32),("p",.pred)]
def observed (width value count : Nat) : Option Nat :=
  ((localStep [] 0 {} (.bin .shr width width "out" (.imm value) (.imm count))).toOption).bind (fun thread => lookup "out" thread.regs)
theorem value_width_and_u32_count : InstructionTyped registers [] 1 (.bin .shr 64 64 "wide" (.reg "bits") (.reg "word")) := by decide
theorem wide_count_rejected : ¬InstructionTyped registers [] 1 (.bin .shr 64 64 "wide" (.reg "bits") (.reg "wide")) := by decide
theorem widening_shift_rejected : ¬InstructionTyped registers [] 1 (.bin .shr 32 64 "wide" (.reg "word") (.imm 4)) := by decide
theorem logical_high_bits : observed 32 4294967295 31 = some 1 ∧ observed 64 9223372036854775808 63 = some 1 := by decide
theorem oversized_counts_zero : observed 32 4294967295 32 = some 0 ∧ observed 64 18446744073709551615 4294967295 = some 0 := by decide
theorem value_width_wraps_before_shift : observed 32 4294967312 4 = some 1 := by decide
theorem count_width_is_not_value_width : observed 64 4294967296 32 = some 1 := by decide

end Ptx.ShiftTests
