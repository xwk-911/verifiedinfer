import Ptx.Kernels.ShufflePair

/-! Global register agreement for the actual three-slot source program. The
oracle family includes wrong replies and predicates; global constraints are
what distinguish the exchange from arbitrary local executions. -/
namespace Ptx.Kernels.ShufflePair
open Ptx.ISA Ptx.Shuffle
noncomputable section

theorem pair_source_iff (left right : Lane2) (a b : Nat) (pa pb : Bool) :
    Source block (event left) (record left a pa) (event right) (record right b pb) ↔ left ≠ right := by
  fin_cases left <;> fin_cases right <;> dsimp [Source,record,event,SameWarp] <;> decide

theorem pair_predicate (which : Lane2) : (select .bfly (lane block (id which)) 1 31).predicate = true := by
  fin_cases which <;> decide

theorem pair_matched (a b : Nat) (pa pb : Bool) (which : Lane2) (value : Nat) (predicate : Bool) :
    Matched block (candidate a b pa pb) (event which) (record which value predicate) := by
  refine ⟨?_,?_⟩
  · fin_cases which <;> dsimp [record,event] <;> decide
  · intro actual ht _ _
    simp only [candidate,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact Or.inl ⟨0,record 0 a pa,lookup_zero a b pa pb,rfl,rfl⟩
    · exact Or.inl ⟨0,record 1 b pb,lookup_one a b pa pb,rfl,rfl⟩

theorem pair_defined (a b : Nat) (pa pb : Bool) : Defined block (candidate a b pa pb) := by
  intro origin result he
  obtain (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) := shuffle_cases he
  · exact ⟨pair_matched a b pa pb 0 a pa,event 1,record 1 b pb,lookup_one a b pa pb,
      (pair_source_iff 0 1 a b pa pb).2 (by decide)⟩
  · exact ⟨pair_matched a b pa pb 1 b pb,event 0,record 0 a pa,lookup_zero a b pa pb,
      (pair_source_iff 1 0 b a pb pa).2 (by decide)⟩

theorem pair_agreement_iff (a b : Nat) (pa pb : Bool) :
    Agreement block (candidate a b pa pb) ↔ wrap 32 a = 1 ∧ pa = true ∧ wrap 32 b = 0 ∧ pb = true := by
  constructor
  · intro ha
    have h0 := ha (event 0) (record 0 a pa) (lookup_zero a b pa pb) (pair_matched a b pa pb 0 a pa)
      (event 1) (record 1 b pb) (lookup_one a b pa pb) ((pair_source_iff 0 1 a b pa pb).2 (by decide))
    have h1 := ha (event 1) (record 1 b pb) (lookup_one a b pa pb) (pair_matched a b pa pb 1 b pb)
      (event 0) (record 0 a pa) (lookup_zero a b pa pb) ((pair_source_iff 1 0 b a pb pa).2 (by decide))
    exact ⟨h0.1,by simpa only [record,key,event,pair_predicate] using h0.2,
      h1.1,by simpa only [record,key,event,pair_predicate] using h1.2⟩
  · rintro ⟨ha,hpa,hb,hpb⟩ origin result he _ peer input hp hs
    obtain (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) := shuffle_cases he
    all_goals obtain (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) := shuffle_cases hp
    · exact False.elim ((pair_source_iff 0 0 a a pa pa).1 hs rfl)
    · exact ⟨ha,by simpa only [record,key,event,pair_predicate] using hpa⟩
    · exact ⟨hb,by simpa only [record,key,event,pair_predicate] using hpb⟩
    · exact False.elim ((pair_source_iff 1 1 b b pb pb).1 hs rfl)

def controlRank : ControlNode → Nat
  | .arrival _ => 0
  | .returned _ => 1
  | .ordinary _ => 0
  | .exited _ => 2

theorem pair_control_admitted (a b : Nat) (pa pb : Bool) : ControlAdmitted block (candidate a b pa pb) := by
  apply control_admitted_of_rank controlRank
  intro left right he
  cases he with
  | «local» => exact Nat.zero_lt_one
  | rendezvous => exact Nat.zero_lt_one
  | po hl hr _ hs =>
    obtain (⟨rfl,_⟩ | ⟨rfl,_⟩) := event_cases hl
    all_goals obtain (⟨rfl,_⟩ | ⟨rfl,_⟩) := event_cases hr
    all_goals exact False.elim (Nat.lt_irrefl 0 hs)
  | exit he _ _ _ =>
    obtain (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) := event_cases he <;> exact Nat.lt_succ_self 1
  | exitedPeer he ht _ _ hx =>
    obtain (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) := shuffle_cases he
    all_goals
      simp only [candidate,List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl
      all_goals exact False.elim (by have : 1 ≤ 0 := hx.2; omega)
  | barrier hl _ _ =>
    obtain (⟨_,hk⟩ | ⟨_,hk⟩) := event_cases hl <;> cases hk

theorem pair_legal_complete_witness (initial : Location → Symbolic.Byte) :
    WellFormed Generated.shuffle_pair.program (launch initial) (candidate 1 0 true true) ∧
    Complete (candidate 1 0 true true) ∧ ControlAdmitted block (candidate 1 0 true true) ∧
    Defined block (candidate 1 0 true true) ∧ Agreement block (candidate 1 0 true true) := by
  exact ⟨actual_source_well_formed 1 0 true true initial,actual_source_complete 1 0 true true,
    pair_control_admitted 1 0 true true,pair_defined 1 0 true true,(pair_agreement_iff 1 0 true true).2 (by decide)⟩

theorem pair_register_correct {a b : Nat} {pa pb : Bool} (ha : Agreement block (candidate a b pa pb)) :
    lookup "%dst" (finalState 0 a pa).base.core.thread.regs = some 1 ∧
    lookup "%dst" (finalState 1 b pb).base.core.thread.regs = some 0 ∧
    lookup "%p" (finalState 0 a pa).base.core.thread.regs = some 1 ∧
    lookup "%p" (finalState 1 b pb).base.core.thread.regs = some 1 := by
  obtain ⟨h0,hpa,h1,hpb⟩ := (pair_agreement_iff a b pa pb).1 ha
  simp [finalState,lookup,put,h0,h1,hpa,hpb]

theorem pair_has_no_ordinary_events (a b : Nat) (pa pb : Bool) :
    (candidate a b pa pb).view.traces.all (fun trace => trace.events.isEmpty) = true := rfl

end
end Ptx.Kernels.ShufflePair
