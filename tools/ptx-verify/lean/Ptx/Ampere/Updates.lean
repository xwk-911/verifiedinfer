import Ptx.Ampere.MmaLocalRules
import Ptx.Scalar.Updates

/-! Packed-register update equations for symbolic execution. They preserve
unrelated bindings and the fixed interpreter's register-bank invalidation. -/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

def intAssign (s : State) (dst : String) (value : Nat) : State := {
  s with
  scalar := Scalar.intAssign s.scalar dst value
  packed := s.packed.filter (fun kv => kv.1 != dst)
}
def intPC (s : State) (pc : Nat) : State := {s with scalar := Scalar.intPC s.scalar pc}

@[simp] theorem intAssign_nat (s : State) (dst name : String) (value : Nat) :
    lookup name (intAssign s dst value).scalar.core.thread.regs =
      if name = dst then some value else lookup name s.scalar.core.thread.regs := Scalar.intAssign_nat _ _ _ _
@[simp] theorem intPC_nat (s : State) (pc : Nat) (name : String) :
    lookup name (intPC s pc).scalar.core.thread.regs = lookup name s.scalar.core.thread.regs := rfl
@[simp] theorem intAssign_pc (s : State) (dst : String) (value : Nat) :
    (intAssign s dst value).scalar.core.thread.pc = s.scalar.core.thread.pc+1 := rfl
@[simp] theorem intPC_pc (s : State) (pc : Nat) : (intPC s pc).scalar.core.thread.pc = pc := rfl
@[simp] theorem intAssign_queries (s : State) (dst : String) (value : Nat) :
    (intAssign s dst value).scalar.core.queries = s.scalar.core.queries := rfl
@[simp] theorem intPC_queries (s : State) (pc : Nat) :
    (intPC s pc).scalar.core.queries = s.scalar.core.queries := rfl
@[simp] theorem intAssign_status (s : State) (dst : String) (value : Nat) :
    (intAssign s dst value).scalar.core.thread.status = s.scalar.core.thread.status := rfl
@[simp] theorem intPC_status (s : State) (pc : Nat) :
    (intPC s pc).scalar.core.thread.status = s.scalar.core.thread.status := rfl

theorem intAssign_float (s : State) (dst name : String) (value : Nat)
    (hd : name ≠ dst) (hn : lookup name s.scalar.core.thread.regs = none) :
    declarationLookup name (intAssign s dst value).scalar.floats = declarationLookup name s.scalar.floats := by
  simp [intAssign,Scalar.intAssign_float,hd,hn]
theorem intPC_float (s : State) (pc : Nat) (name : String)
    (hn : lookup name s.scalar.core.thread.regs = none) :
    declarationLookup name (intPC s pc).scalar.floats = declarationLookup name s.scalar.floats := by
  simp [intPC,Scalar.intPC_float,hn]

theorem integer_lookup_filter (name : String) (test : String → Bool) (bindings : Bindings) :
    lookup name (bindings.filter (fun kv => test kv.1)) = if test name then lookup name bindings else none := by
  induction bindings with
  | nil => simp [lookup]
  | cons head tail ih =>
    rcases head with ⟨key,value⟩
    by_cases hk : key = name
    · subst key
      by_cases ht : test name = true <;> simp [lookup,ht,ih]
    · by_cases ht : test key = true <;> simp [lookup,hk,ht,ih]

@[simp] theorem mma_nat (s : State) (d : Registers4) (output : Fin 4 → ℝ) (name : String) :
    lookup name (mmaAction s d output).scalar.core.thread.regs =
      if d.names.contains name then none else lookup name s.scalar.core.thread.regs := by
  change lookup name (s.scalar.core.thread.regs.filter (fun kv => !d.names.contains kv.1)) = _
  rw [integer_lookup_filter name (fun key => !d.names.contains key) s.scalar.core.thread.regs]
  cases h : d.names.contains name <;> simp [h]

@[simp] theorem packed_word_nat (s : State) (dst name : String) (pair : PackedF16) :
    lookup name (wordAction s dst (.packed pair)).scalar.core.thread.regs =
      if name = dst then none else lookup name s.scalar.core.thread.regs := by
  by_cases hn : name = dst
  · subst name
    simp [wordAction,advance,Scalar.integer_lookup_filter_same]
  · simpa only [wordAction,advance,Ptx.advance,hn,ite_false] using (lookup_filter_other hn s.scalar.core.thread.regs)

@[simp] theorem packed_word_float (s : State) (dst name : String) (pair : PackedF16) :
    declarationLookup name (wordAction s dst (.packed pair)).scalar.floats =
      if name = dst then none else declarationLookup name s.scalar.floats := by
  change declarationLookup name (s.scalar.floats.filter (fun kv => kv.1 != dst)) = _
  rw [Scalar.lookup_filter_name name (fun key => key != dst) s.scalar.floats]
  by_cases hn : name = dst <;> simp [hn]

@[simp] theorem packed_word_packed (s : State) (dst name : String) (pair : PackedF16) :
    declarationLookup name (wordAction s dst (.packed pair)).packed =
      if name = dst then some pair else declarationLookup name s.packed := by
  change declarationLookup name ((dst,pair)::s.packed.filter (fun kv => kv.1 != dst)) = _
  by_cases hn : name = dst
  · subst name
    simp [declarationLookup]
  · simp only [declarationLookup,show (dst == name) = false from by simp [Ne.symm hn],Bool.false_eq_true,ite_false]
    rw [Scalar.lookup_filter_name name (fun key => key != dst) s.packed]
    simp [hn]

@[simp] theorem packed_word_pc (s : State) (dst : String) (pair : PackedF16) :
    (wordAction s dst (.packed pair)).scalar.core.thread.pc = s.scalar.core.thread.pc+1 := rfl
@[simp] theorem packed_word_queries (s : State) (dst : String) (pair : PackedF16) :
    (wordAction s dst (.packed pair)).scalar.core.queries = s.scalar.core.queries+1 := rfl
@[simp] theorem packed_word_status (s : State) (dst : String) (pair : PackedF16) :
    (wordAction s dst (.packed pair)).scalar.core.thread.status = s.scalar.core.thread.status := rfl

end
end Ptx.Ampere
