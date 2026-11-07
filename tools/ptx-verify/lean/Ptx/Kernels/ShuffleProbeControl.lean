import Ptx.Kernels.ShuffleProbeSafety

/-! Source-derived control admission for every completed exported-probe trace.
Ordinary nodes use original source serials; this is not a memory fence or a
physical progress/fairness theorem. -/
namespace Ptx.Kernels.ShuffleProbe
open Ptx.ISA Ptx.Shuffle
noncomputable section

def controlRank : ControlNode → Nat
  | .arrival _ => 0
  | .returned _ => 1
  | .ordinary actual => actual.serial+1
  | .exited _ => 4

theorem final_generation (mode : Mode) (input : Inputs) (ctx : Scalar.Context) (value : Nat) (predicate : Bool) :
    Shuffle.generation (finalState mode input ctx value predicate) (groupKey mode input) = 1 := by
  have hv : (finalState mode input ctx value predicate).visits = [(groupKey mode input,1)] := by cases predicate <;> rfl
  simp [Shuffle.generation,hv]

theorem actual_event_ranks {mode input launch candidate actual kind} (hp : Params input launch.params)
    (hw : Shuffle.WellFormed (code mode) launch candidate) (hc : Shuffle.Complete candidate)
    (he : candidate.eventAt actual = some kind) :
    controlRank (finishNode actual kind) = actual.serial+1 ∧
    controlRank (startNode actual kind) = (if actual.serial = 0 then 0 else actual.serial+1) ∧ actual.serial < 3 := by
  obtain ⟨trace,_,_,hget⟩ := actual_event_shape hp hw hc he
  cases hn : actual.serial with
  | zero =>
    simp only [hn,events,List.getElem?_cons_zero,Option.some.injEq] at hget
    subst kind
    simp [controlRank,startNode,finishNode,hn]
  | succ serial =>
    cases serial with
    | zero =>
      simp only [hn,events,outputEvents,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at hget
      subst kind
      simp [controlRank,startNode,finishNode,hn]
    | succ serial =>
      cases serial with
      | zero =>
        simp only [hn,events,outputEvents,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at hget
        subst kind
        simp [controlRank,startNode,finishNode,hn]
      | succ serial => simp [hn,events,outputEvents] at hget

theorem no_source_barrier_arrivals {mode input launch candidate actual bid generation}
    (hp : Params input launch.params) (hw : Shuffle.WellFormed (code mode) launch candidate)
    (hc : Shuffle.Complete candidate) : candidate.eventAt actual ≠ some (.ordinary (.barrierArrival bid generation)) := by
  intro he
  obtain ⟨_,_,_,hget⟩ := actual_event_shape hp hw hc he
  have hm := List.mem_of_getElem? hget
  simp [events,outputEvents] at hm

theorem all_completed_control_admitted {mode input launch candidate} (hp : Params input launch.params)
    (hw : Shuffle.WellFormed (code mode) launch candidate) (hc : Shuffle.Complete candidate) :
    ControlAdmitted launch.geometry.block candidate := by
  apply control_admitted_of_rank controlRank
  intro left right he
  cases he with
  | «local» => exact Nat.zero_lt_one
  | rendezvous => exact Nat.zero_lt_one
  | @po leftId rightId before after hl hr _ hs =>
    have hleft := actual_event_ranks hp hw hc hl
    have hright := actual_event_ranks hp hw hc hr
    rw [hleft.1,hright.2.1]
    have hn : rightId.serial ≠ 0 := by omega
    simp only [hn,ite_false]
    omega
  | exit he _ _ _ =>
    have hr := actual_event_ranks hp hw hc he
    change controlRank (finishNode _ _) < 4
    rw [hr.1]
    omega
  | exitedPeer he ht _ _ hx =>
    obtain ⟨_,_,_,_,hr⟩ := actual_shuffle_shape hp hw hc he
    rw [hr] at hx
    have hgen := hx.2
    rw [(member_source_shape hp hw hc ht).2.1] at hgen
    change Shuffle.generation (finalState mode input _ _ _) (groupKey mode input) ≤ 0 at hgen
    rw [final_generation] at hgen
    omega
  | barrier hl _ _ => exact False.elim (no_source_barrier_arrivals hp hw hc hl)

end
end Ptx.Kernels.ShuffleProbe
