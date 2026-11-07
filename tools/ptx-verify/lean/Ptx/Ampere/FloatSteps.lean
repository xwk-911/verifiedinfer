import Ptx.Ampere.ScalarSteps

/-! Scalar float updates inside the extended interpreter. The packed-bank
invalidation is the one performed by actual scalar source instructions. -/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

def floatAssign (s : State) (dst : String) (format : Symbolic.Format) (value : ℝ) : State := {
  s with
  scalar := Scalar.writeFloat s.scalar dst format value
  packed := s.packed.filter (fun kv => kv.1 != dst)
}

theorem move_float_step {ctx oracle code s dst format src value}
    (hr : s.scalar.core.thread.status = .running)
    (hi : code[s.scalar.core.thread.pc]? = some (.scalar (.mov format dst src)))
    (hv : Scalar.eval format s.scalar src = .ok value) :
    step ctx oracle code s = .ok (floatAssign s dst format value,[]) := by
  simpa [floatAssign,finishScalar,scalarWritten] using scalar_step hr hi
    (Scalar.mov_float_step hr (scalarSkeleton_slot hi) hv)

@[simp] theorem floatAssign_nat (s : State) (dst name : String) (format : Symbolic.Format) (value : ℝ) :
    lookup name (floatAssign s dst format value).scalar.core.thread.regs =
      if name = dst then none else lookup name s.scalar.core.thread.regs := Scalar.writeFloat_nat _ _ _ _ _
@[simp] theorem floatAssign_float (s : State) (dst name : String) (format : Symbolic.Format) (value : ℝ) :
    declarationLookup name (floatAssign s dst format value).scalar.floats =
      if name = dst then some (format,value) else declarationLookup name s.scalar.floats := Scalar.writeFloat_float _ _ _ _ _
@[simp] theorem floatAssign_pc (s : State) (dst : String) (format : Symbolic.Format) (value : ℝ) :
    (floatAssign s dst format value).scalar.core.thread.pc = s.scalar.core.thread.pc+1 := rfl
@[simp] theorem floatAssign_queries (s : State) (dst : String) (format : Symbolic.Format) (value : ℝ) :
    (floatAssign s dst format value).scalar.core.queries = s.scalar.core.queries := rfl
@[simp] theorem floatAssign_status (s : State) (dst : String) (format : Symbolic.Format) (value : ℝ) :
    (floatAssign s dst format value).scalar.core.thread.status = s.scalar.core.thread.status := rfl

end
end Ptx.Ampere
