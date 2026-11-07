import Ptx.Scalar.Rules

/-! Register-update normal forms for symbolic execution of mixed scalar blocks.
They retain the fixed interpreter's cross-bank invalidation and arbitrary
unrelated bindings; they do not replace program instructions with new meanings.
-/
namespace Ptx.Scalar
open Ptx.ISA
noncomputable section

def intAssign (s : State) (dst : String) (value : Nat) : State :=
  finishInteger s {s.core with thread := assign s.core.thread dst value}
def intPC (s : State) (pc : Nat) : State :=
  finishInteger s {s.core with thread := {s.core.thread with pc := pc}}
def loadedFloat (s : State) (dst : String) (value : ℝ) : State :=
  let next := writeFloat s dst .f32 value
  {next with core := {next.core with queries := s.core.queries+1}}

def loadedInteger (s : State) (dst : String) (value : Nat) : State :=
  finishInteger s {s.core with thread := assign s.core.thread dst (wrap 32 value),queries := s.core.queries+1}

@[simp] theorem loadedInteger_nat (s : State) (dst name : String) (value : Nat) :
    lookup name (loadedInteger s dst value).core.thread.regs =
      if name = dst then some (wrap 32 value) else lookup name s.core.thread.regs := by
  by_cases h : name = dst
  · subst name; simp [loadedInteger,finishInteger,assign]
  · simp [loadedInteger,finishInteger,assign,h]

@[simp] theorem intAssign_nat (s : State) (dst name : String) (value : Nat) :
    lookup name (intAssign s dst value).core.thread.regs =
      if name = dst then some value else lookup name s.core.thread.regs := by
  by_cases h : name = dst
  · subst name; simp [intAssign,finishInteger,assign]
  · simp [intAssign,finishInteger,assign,h]

@[simp] theorem intPC_nat (s : State) (pc : Nat) (name : String) :
    lookup name (intPC s pc).core.thread.regs = lookup name s.core.thread.regs := rfl

@[simp] theorem writeFloat_nat (s : State) (dst name : String) (format : Symbolic.Format) (value : ℝ) :
    lookup name (writeFloat s dst format value).core.thread.regs =
      if name = dst then none else lookup name s.core.thread.regs := by
  by_cases h : name = dst
  · subst name; simp only [ite_true]; exact float_write_invalidates_integer _ _ _ _
  · simpa only [h,ite_false] using (float_write_frame s dst name format value h).2

@[simp] theorem loadedFloat_nat (s : State) (dst name : String) (value : ℝ) :
    lookup name (loadedFloat s dst value).core.thread.regs =
      if name = dst then none else lookup name s.core.thread.regs := by
  simpa only [loadedFloat] using writeFloat_nat s dst name .f32 value

@[simp] theorem writeFloat_float (s : State) (dst name : String) (format : Symbolic.Format) (value : ℝ) :
    declarationLookup name (writeFloat s dst format value).floats =
      if name = dst then some (format,value) else declarationLookup name s.floats := by
  by_cases h : name = dst
  · subst name; simp only [ite_true]; exact float_write_lookup _ _ _ _
  · simpa only [h,ite_false] using (float_write_frame s dst name format value h).1

@[simp] theorem loadedFloat_float (s : State) (dst name : String) (value : ℝ) :
    declarationLookup name (loadedFloat s dst value).floats =
      if name = dst then some (.f32,value) else declarationLookup name s.floats := by
  simpa only [loadedFloat] using writeFloat_float s dst name .f32 value

@[simp] theorem intAssign_float (s : State) (dst name : String) (value : Nat) :
    declarationLookup name (intAssign s dst value).floats =
      if (if name = dst then some value else lookup name s.core.thread.regs) = none
      then declarationLookup name s.floats else none := by
  unfold intAssign
  rw [finish_integer_lookup]
  by_cases h : name = dst
  · subst name; simp [assign]
  · simp [assign,h]

@[simp] theorem intPC_float (s : State) (pc : Nat) (name : String) :
    declarationLookup name (intPC s pc).floats =
      if lookup name s.core.thread.regs = none then declarationLookup name s.floats else none := by
  exact finish_integer_lookup _ _ _

theorem float_value_no_integer {s : State} (hd : BanksDisjoint s) {name format value}
    (hf : declarationLookup name s.floats = some (format,value)) : lookup name s.core.thread.regs = none := by
  rcases hd name with h | h
  · exact h
  · rw [h] at hf
    cases hf

@[simp] theorem wrap_idempotent (width value : Nat) : wrap width (wrap width value) = wrap width value := by
  simp [wrap]

theorem wrap_add (width a b : Nat) : wrap width (wrap width a + wrap width b) = wrap width (a+b) := by
  simp [wrap,Nat.add_mod]

theorem wrap_add_left (width a b : Nat) : wrap width (wrap width a+b) = wrap width (a+b) := by
  simp [wrap,Nat.add_mod]

theorem wrap_add_right (width a b : Nat) : wrap width (a+wrap width b) = wrap width (a+b) := by
  simp [wrap,Nat.add_mod]

theorem wrap_mul (width a b : Nat) : wrap width (wrap width a*wrap width b) = wrap width (a*b) := by
  simp [wrap,Nat.mul_mod]

end
end Ptx.Scalar
