import Ptx.Ampere.Thread

/-! Register exclusivity and instruction counters for source-local MMA/word
operations. Arithmetic of oracle results is constrained separately per warp. -/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

theorem scalar_clears_packed (s : State) (i : Scalar.Instr) (next : Scalar.State) (dst : String)
    (hw : scalarWritten i = some dst) (pair : PackedF16) : (dst,pair) ∉ (finishScalar s i next).packed := by
  simp [finishScalar,hw]
theorem integer_word_clears_packed (s : State) (dst : String) (n : Nat) (pair : PackedF16) :
    (dst,pair) ∉ (wordAction s dst (.integer n)).packed := by
  simp [wordAction]
theorem packed_word_clears_integer (s : State) (dst : String) (pair : PackedF16) (n : Nat) :
    (dst,n) ∉ (wordAction s dst (.packed pair)).scalar.core.thread.regs := by
  simp [wordAction,advance]
theorem packed_word_clears_float (s : State) (dst : String) (pair : PackedF16) (f : Symbolic.Format × ℝ) :
    (dst,f) ∉ (wordAction s dst (.packed pair)).scalar.floats := by
  simp [wordAction,advance]
theorem mma_clears_packed (s : State) (d : Registers4) (output : Fin 4 → ℝ) {name : String}
    (hn : name ∈ d.names) (pair : PackedF16) : (name,pair) ∉ (mmaAction s d output).packed := by
  simp [mmaAction,advance,hn]
theorem mma_clears_integer (s : State) (d : Registers4) (output : Fin 4 → ℝ) {name : String}
    (hn : name ∈ d.names) (n : Nat) : (name,n) ∉ (mmaAction s d output).scalar.core.thread.regs := by
  simp [mmaAction,advance,hn]
theorem mma_pc_once (s : State) (d : Registers4) (output : Fin 4 → ℝ) :
    (mmaAction s d output).scalar.core.thread.pc = s.scalar.core.thread.pc+1 := rfl
theorem mma_query_once (s : State) (d : Registers4) (output : Fin 4 → ℝ) :
    (mmaAction s d output).scalar.core.queries = s.scalar.core.queries+1 := rfl
theorem mma_ordinal_once (s : State) (d : Registers4) (output : Fin 4 → ℝ) :
    (mmaAction s d output).mmaCalls = s.mmaCalls+1 := rfl

end
end Ptx.Ampere
