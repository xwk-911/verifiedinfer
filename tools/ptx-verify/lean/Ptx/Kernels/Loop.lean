import Ptx.Generated.Loop
import Ptx.Rules.Local

/-! External, instruction-indexed invariant for the actual generated loop kernel.
The loop bound is the PTX literal 4. Thread count, scheduler, memory contents,
parameter environment and initial register contents are universally quantified. -/
namespace Ptx.LoopContract
abbrev code := Generated.loop.program

def Stage (t : Thread) : Prop :=
  match t.pc with
  | 0 => True
  | 1 => ∃ k, k < 4 ∧ lookup "%r" t.regs = some k
  | 2 => ∃ k, 0 < k ∧ k ≤ 4 ∧ lookup "%r" t.regs = some k
  | 3 => ∃ k, 0 < k ∧ k ≤ 4 ∧ lookup "%r" t.regs = some k ∧
      lookup "%p" t.regs = some (if k < 4 then 1 else 0)
  | 4 => lookup "%r" t.regs = some 4
  | _ => False

def Inv (t : Thread) : Prop :=
  (t.status = .running ∧ Stage t) ∨
  (t.status = .done ∧ t.pc = 4 ∧ lookup "%r" t.regs = some 4)

theorem wrap32_small {k : Nat} (hk : k ≤ 4) : wrap 32 k = k := by
  apply Nat.mod_eq_of_lt
  have h : 4 < 2^32 := by decide
  omega

theorem local_invariant : LocalInvariant code Inv := by
  constructor
  · intro t hi
    rcases hi with ⟨hr,_⟩ | ⟨hd,_⟩
    · exact Or.inl hr
    · exact Or.inr hd
  · intro params tid t hi hr
    rcases hi with ⟨_,hst⟩ | ⟨hd,_⟩
    · match hpc : t.pc with
      | 0 =>
        refine ⟨.mov 32 "%r" (.imm 0), assign t "%r" 0, ?_, rfl, ?_, ?_⟩
        · simp [code, Generated.loop.program]
        · simp [localStep, eval, wrap, bind, Except.bind, pure, Except.pure]
        · left; constructor
          · simpa [assign, advance] using hr
          · simp [Stage, assign, advance, hpc]
      | 1 =>
        obtain ⟨k,hk,hv⟩ := (by simpa [Stage, hpc] using hst : ∃ k, k < 4 ∧ lookup "%r" t.regs = some k)
        have hw : wrap 32 k = k := wrap32_small (by omega)
        have hw' : wrap 32 (k+1) = k+1 := wrap32_small (by omega)
        refine ⟨.bin .add 32 32 "%r" (.reg "%r") (.imm 1), assign t "%r" (k+1), ?_, rfl, ?_, ?_⟩
        · simp [code, Generated.loop.program]
        · simp [localStep, eval, hv, hw, hw', bind, Except.bind, pure, Except.pure, wrap32_small (by decide : 1 ≤ 4)]
        · left; constructor
          · simpa [assign, advance] using hr
          · simp only [Stage, assign, advance, hpc, Nat.reduceAdd]
            exact ⟨k+1, by omega, by omega, lookup_put_same _ _ _⟩
      | 2 =>
        obtain ⟨k,hpos,hk,hv⟩ := (by simpa [Stage, hpc] using hst : ∃ k, 0 < k ∧ k ≤ 4 ∧ lookup "%r" t.regs = some k)
        let p := if k < 4 then 1 else 0
        refine ⟨.setp .lt "%p" (.reg "%r") (.imm 4), assign t "%p" p, ?_, rfl, ?_, ?_⟩
        · simp [code, Generated.loop.program]
        · simp [localStep, eval, hv, wrap32_small hk, wrap32_small (by decide : 4 ≤ 4), p,
            bind, Except.bind, pure, Except.pure]
        · left; constructor
          · simpa [assign, advance] using hr
          · simp only [Stage, assign, advance, hpc, Nat.reduceAdd]
            exact ⟨k,hpos,hk, by simpa using hv, lookup_put_same _ _ _⟩
      | 3 =>
        obtain ⟨k,hpos,hk,hv,hp⟩ := (by simpa [Stage, hpc] using hst : ∃ k, 0 < k ∧ k ≤ 4 ∧ lookup "%r" t.regs = some k ∧ lookup "%p" t.regs = some (if k < 4 then 1 else 0))
        by_cases hlt : k < 4
        · refine ⟨.branch "%p" true 1, { t with pc := 1 }, ?_, rfl, ?_, ?_⟩
          · simp [code, Generated.loop.program]
          · simp [localStep, hp, hlt, bind, Except.bind, pure, Except.pure]
          · exact Or.inl ⟨hr, k,hlt,hv⟩
        · have heq : k = 4 := by omega
          refine ⟨.branch "%p" true 1, { t with pc := 4 }, ?_, rfl, ?_, ?_⟩
          · simp [code, Generated.loop.program]
          · simp [localStep, hp, hlt, hpc, bind, Except.bind, pure, Except.pure]
          · exact Or.inl ⟨hr, by simpa [Stage, heq] using hv⟩
      | 4 =>
        have hv : lookup "%r" t.regs = some 4 := by simpa [Stage, hpc] using hst
        refine ⟨.ret, { t with status := .done }, ?_, rfl, rfl, Or.inr ⟨rfl,hpc,hv⟩⟩
        simp [code, Generated.loop.program]
      | _ + 5 => simp [Stage, hpc] at hst
    · simp_all

def Pre (m : Machine) : Prop :=
  ∀ t ∈ m.threads, t.pc = 0 ∧ t.status = .running
def Post (m : Machine) : Prop := ∀ t ∈ m.threads, lookup "%r" t.regs = some 4

theorem pre_invariant {m} (hp : Pre m) : AllThreads Inv m := by
  intro t ht
  obtain ⟨hpc,hr⟩ := hp t ht
  exact Or.inl ⟨hr, by simp [Stage, hpc]⟩

/-- Safety covers every runnable thread after every finite interleaving. -/
theorem safe : Safe code Pre := by
  intro m m' hp hs
  exact localInvariant_safe local_invariant m m' (pre_invariant hp) hs

/-- Every reached output in a finished execution is exactly 4. No fairness premise. -/
theorem correct : Triple code Pre Post := by
  refine invariant_rule (code := code) (P := Pre) (Q := Post) (I := AllThreads Inv) ?_ ?_ ?_
  · intro m hp; exact pre_invariant hp
  · exact localInvariant_inductive local_invariant
  · intro m hi hd t ht
    have hdone : t.status = .done := by
      have := List.all_eq_true.mp hd t ht
      simpa using this
    rcases hi t ht with ⟨hr,_⟩ | ⟨_,_,hv⟩
    · simp_all
    · exact hv

theorem progress {m m'} (hp : Pre m) (hs : Steps code m m')
    (hn : m'.threads.all (fun t => t.status == .done) ≠ true) :
    ∃ tid next, threadStep code tid m' = .ok next :=
  localInvariant_progress local_invariant
    (invariant_steps (localInvariant_inductive local_invariant) hs (pre_invariant hp)) hn

theorem frame {m m'} (hp : Pre m) (hs : Steps code m m') : SameEnvironment m m' :=
  localInvariant_frame local_invariant (pre_invariant hp) hs

end Ptx.LoopContract
