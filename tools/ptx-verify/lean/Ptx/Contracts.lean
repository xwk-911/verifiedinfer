import Ptx.Semantics

namespace Ptx
abbrev Assertion := Machine → Prop

/-- Partial correctness for ALL finite executions, not just a chosen schedule. -/
def Triple (code : List Instr) (P Q : Assertion) : Prop :=
  ∀ m m', P m → Steps code m m' → m'.threads.all (fun t => t.status == .done) → Q m'

/-- Instruction-indexed invariants live in separate specification files. -/
def InductiveInvariant (code : List Instr) (I : Assertion) : Prop :=
  ∀ m a m', I m → step code a m = .ok m' → I m'

theorem invariant_steps {code I} (preserve : InductiveInvariant code I)
    {m m'} (h : Steps code m m') (hi : I m) : I m' := by
  induction h with
  | refl => exact hi
  | next a hs _ ih => exact ih (preserve _ a _ hi hs)

theorem invariant_rule {code P Q I}
    (init : ∀ m, P m → I m) (preserve : InductiveInvariant code I)
    (exit : ∀ m, I m → m.threads.all (fun t => t.status == .done) → Q m) : Triple code P Q := by
  intro m m' hp hs hd
  exact exit m' (invariant_steps preserve hs (init m hp)) hd

/-- Safety must be proved separately: partial correctness alone could be vacuous. -/
def Safe (code : List Instr) (P : Assertion) : Prop :=
  ∀ m m', P m → Steps code m m' → ∀ tid t,
    m'.threads[tid]? = some t → t.status = .running → ∃ next, threadStep code tid m' = .ok next

end Ptx
