import Ptx.Ampere.Thread

/-! Source-derived ledger facts. Every issued operation stays at its original
ordinal through later source steps. No heap mutation/completion follows merely
from issuing or committing a copy. -/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

theorem copy_step {ctx oracle code s cache dst src size srcAddr dstAddr}
    (hr : s.scalar.core.thread.status = .running)
    (hi : code[s.scalar.core.thread.pc]? = some (.copy cache dst src size))
    (ht : CopySize cache size)
    (hs : evalAddr ctx.id.tid.x s.scalar.core.thread src = .ok srcAddr)
    (hd : evalAddr ctx.id.tid.x s.scalar.core.thread dst = .ok dstAddr)
    (hb : (oracle.bytes s.scalar.core.queries).length = size) :
    step ctx oracle code s = .ok (issue s ⟨cache,s.groups,⟨.global,srcAddr⟩,
      ⟨.shared ctx.id.cta,dstAddr⟩,oracle.bytes s.scalar.core.queries⟩) := by
  simp [step,hr,hi,ht,hs,hd,hb,liftInteger,bind,Except.bind,pure,Except.pure]

structure Evolution (s next : State) (events : List Event) : Prop where
  groups_mono : s.groups ≤ next.groups
  extension : ∃ added, next.copies = s.copies ++ added
  recorded : ∀ ordinal op, Event.issue ordinal op ∈ events → next.copies[ordinal]? = some op
  origins : ∀ ordinal op, next.copies[ordinal]? = some op →
    s.copies[ordinal]? = some op ∨ Event.issue ordinal op ∈ events

theorem ordinary_evolution (s : State) (next : Scalar.State) (emitted : List Scalar.Kind) :
    Evolution s {s with scalar := next} (emitted.map Event.ordinary) := by
  refine ⟨Nat.le_refl _,⟨[],by simp⟩,?_,?_⟩
  · intro ordinal op hm
    obtain ⟨kind,_,he⟩ := List.mem_map.mp hm
    cases he
  · intro ordinal op ho
    exact .inl ho

theorem finish_scalar_evolution (s : State) (i : Scalar.Instr) (next : Scalar.State) (emitted : List Scalar.Kind) :
    Evolution s (finishScalar s i next) (emitted.map Event.ordinary) := by
  have h := ordinary_evolution s next emitted
  exact ⟨h.groups_mono,h.extension,h.recorded,h.origins⟩
theorem word_evolution (s : State) (dst : String) (value : Word32) (loc : Location) :
    Evolution s (wordAction s dst value) [.ordinary (.read loc value.encode)] := by
  cases value <;> refine ⟨Nat.le_refl _,⟨[],by simp [wordAction,advance]⟩,?_,?_⟩
  all_goals first
    | intro ordinal op hm; simp at hm
    | intro ordinal op ho; exact .inl ho
theorem mma_evolution (s : State) (d : Registers4) (output : Fin 4 → ℝ) (call : MmaCall) :
    Evolution s (mmaAction s d output) [.mmaEntry call,.mmaReturn call] := by
  refine ⟨Nat.le_refl _,⟨[],by simp [mmaAction,advance]⟩,?_,?_⟩
  · intro ordinal op hm
    simp at hm
  · intro ordinal op ho
    exact .inl ho
theorem issue_evolution (s : State) (op : Copy) : Evolution s (issue s op).1 (issue s op).2 := by
  refine ⟨Nat.le_refl _,⟨[op],rfl⟩,?_,?_⟩
  · intro ordinal actual hm
    have he : Event.issue ordinal actual = Event.issue s.copies.length op := List.mem_singleton.mp hm
    cases he
    simp [issue]
  · intro ordinal actual ho
    change (s.copies++[op])[ordinal]? = some actual at ho
    by_cases hi : ordinal < s.copies.length
    · exact .inl (by simpa only [List.getElem?_append_left hi] using ho)
    · have hb := (List.getElem?_eq_some_iff.mp ho).1
      have heq : ordinal = s.copies.length := by simp only [List.length_append,List.length_singleton] at hb; omega
      subst ordinal
      have hvalue : actual = op := by simpa using ho.symm
      subst actual
      exact .inr (List.mem_singleton_self _)
theorem commit_evolution (s : State) : Evolution s {advance s with groups := s.groups+1} [.commit s.groups] := by
  refine ⟨by change s.groups ≤ s.groups+1; omega,⟨[],by simp [advance]⟩,?_,?_⟩
  · intro ordinal op hm
    have he := List.mem_singleton.mp hm
    cases he
  · intro ordinal op ho
    exact .inl ho
theorem wait_evolution (s : State) (keep : Nat) : Evolution s (advance s) [.wait s.groups keep] := by
  refine ⟨Nat.le_refl _,⟨[],by simp [advance]⟩,?_,?_⟩
  · intro ordinal op hm
    have he := List.mem_singleton.mp hm
    cases he
  · intro ordinal op ho
    exact .inl ho
theorem wait_all_evolution (s : State) : Evolution s {advance s with groups := s.groups+1}
    [.commit s.groups,.wait (s.groups+1) 0] := by
  refine ⟨by change s.groups ≤ s.groups+1; omega,⟨[],by simp [advance]⟩,?_,?_⟩
  · intro ordinal op hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with he | he <;> cases he
  · intro ordinal op ho
    exact .inl ho

theorem step_evolution {ctx oracle code s next emitted}
    (h : step ctx oracle code s = .ok (next,emitted)) : Evolution s next emitted := by
  by_cases hr : s.scalar.core.thread.status = .running
  · cases hi : code[s.scalar.core.thread.pc]? with
    | none => simp [step,hr,hi,bind,Except.bind] at h
    | some instruction =>
      cases instruction with
      | scalar i =>
        cases hs : Scalar.step ctx oracle.scalar (scalarSkeleton code) s.scalar with
        | error fault => simp [step,hr,hi,hs,liftScalar,bind,Except.bind] at h
        | ok result =>
          have he := (scalar_step hr hi hs).symm.trans h
          cases Except.ok.inj he
          exact finish_scalar_evolution _ _ _ _
      | copy cache dst src size =>
        by_cases ht : CopySize cache size
        · cases hs : evalAddr ctx.id.tid.x s.scalar.core.thread src with
          | error fault => simp [step,hr,hi,ht,hs,liftInteger,bind,Except.bind] at h
          | ok srcAddr =>
            cases hd : evalAddr ctx.id.tid.x s.scalar.core.thread dst with
            | error fault => simp [step,hr,hi,ht,hs,hd,liftInteger,bind,Except.bind] at h
            | ok dstAddr =>
              by_cases hb : (oracle.bytes s.scalar.core.queries).length = size
              · have he := (copy_step hr hi ht hs hd hb).symm.trans h
                cases Except.ok.inj he
                exact issue_evolution _ _
              · simp [step,hr,hi,ht,hs,hd,hb,liftInteger,bind,Except.bind] at h
        · simp [step,hr,hi,ht,bind,Except.bind] at h
      | commit =>
        have he := (commit_step hr hi).symm.trans h
        cases Except.ok.inj he
        exact commit_evolution _
      | wait keep =>
        by_cases hk : keep < 8
        · have he := (wait_step hr hi hk).symm.trans h
          cases Except.ok.inj he
          exact wait_evolution _ _
        · simp [step,hr,hi,Nat.le_of_not_gt hk,bind,Except.bind] at h
      | waitAll =>
        have he := (wait_all_step hr hi).symm.trans h
        cases Except.ok.inj he
        exact wait_all_evolution _
      | loadWord32 space dst address =>
        cases ha : evalAddr ctx.id.tid.x s.scalar.core.thread address with
        | error fault => simp [step,hr,hi,ha,liftInteger,bind,Except.bind] at h
        | ok addr =>
          have he := (word_step hr hi ha).symm.trans h
          cases Except.ok.inj he
          exact word_evolution _ _ _ _
      | mma d a b c =>
        by_cases hd : d.names.Nodup
        · cases hin : readMmaInputs s a b c with
          | error fault => simp [step,hr,hi,hd,hin,bind,Except.bind] at h
          | ok inputs =>
            have he := (mma_step hr hi hd hin).symm.trans h
            cases Except.ok.inj he
            exact mma_evolution _ _ _ _
        · simp [step,hr,hi,hd,bind,Except.bind] at h
  · simp [step,hr,bind,Except.bind] at h

theorem evolution_preserves {s next events} {ordinal : Nat} {op : Copy} (he : Evolution s next events)
    (ho : s.copies[ordinal]? = some op) : next.copies[ordinal]? = some op := by
  obtain ⟨added,hc⟩ := he.extension
  rw [hc,List.getElem?_append_left (List.getElem?_eq_some_iff.mp ho).1]
  exact ho

theorem run_evolution {ctx oracle code n s next emitted}
    (h : run ctx oracle code n s = .ok (next,emitted)) : Evolution s next emitted := by
  induction n generalizing s next emitted with
  | zero =>
    cases Except.ok.inj h
    refine ⟨Nat.le_refl _,⟨[],by simp⟩,?_,?_⟩
    · intro ordinal op hm
      cases hm
    · intro ordinal op ho
      exact .inl ho
  | succ n ih =>
    cases hs : step ctx oracle code s with
    | error fault => simp [run,hs,Except.bind] at h
    | ok head =>
      cases ht : run ctx oracle code n head.1 with
      | error fault => simp [run,hs,ht,Except.bind] at h
      | ok tail =>
        have he : (tail.1,head.2++tail.2) = (next,emitted) := Except.ok.inj (by simpa only [run,hs,ht,Except.bind] using h)
        cases he
        have ha := step_evolution hs
        have hb := ih ht
        refine ⟨Nat.le_trans ha.groups_mono hb.groups_mono,?_,?_,?_⟩
        · obtain ⟨a,hea⟩ := ha.extension
          obtain ⟨b,heb⟩ := hb.extension
          exact ⟨a++b,by rw [heb,hea,List.append_assoc]⟩
        · intro ordinal op hm
          rcases List.mem_append.mp hm with hfirst | htail
          · exact evolution_preserves hb (ha.recorded ordinal op hfirst)
          · exact hb.recorded ordinal op htail
        · intro ordinal op ho
          rcases hb.origins ordinal op ho with hmid | htail
          · rcases ha.origins ordinal op hmid with hstart | hfirst
            · exact .inl hstart
            · exact .inr (List.mem_append_left _ hfirst)
          · exact .inr (List.mem_append_right _ htail)

end
end Ptx.Ampere
