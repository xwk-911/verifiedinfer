import Ptx.Kernels.ShufflePairSource
import Ptx.Event.Empty

/-! Safety, final registers and memory frame for every completed source-valid
execution of the fixed two-lane kernel. Source runs and oracle replies are
arbitrary. Separate complete execution/memory/observer witnesses rule out
vacuity; this is still a register-only kernel, not a full-warp exported probe. -/
namespace Ptx.Kernels.ShufflePair
open Ptx.ISA Ptx.Shuffle
noncomputable section

theorem actual_matched {launch candidate} (hp : Pre launch)
    (hw : Shuffle.WellFormed Generated.shuffle_pair.program launch candidate) (hc : Shuffle.Complete candidate)
    (which : Lane2) (value : Nat) (predicate : Bool) :
    Matched block candidate (event which) (record which value predicate) := by
  refine ⟨?_,?_⟩
  · fin_cases which <;> dsimp [record,event] <;> decide
  · intro actual ht _ _
    obtain ⟨other,hi,_,_,_⟩ := member_source_shape hp hw hc ht
    obtain ⟨v,p,he⟩ := each_lane_arrives hp hw hc other
    exact Or.inl ⟨0,record other v p,by simpa only [hi,event] using he,rfl,rfl⟩

theorem actual_defined {launch candidate} (hp : Pre launch)
    (hw : Shuffle.WellFormed Generated.shuffle_pair.program launch candidate) (hc : Shuffle.Complete candidate) :
    Defined block candidate := by
  intro origin result he
  obtain ⟨which,value,predicate,rfl,rfl⟩ := actual_shuffle_shape hp hw hc he
  refine ⟨actual_matched hp hw hc which value predicate,?_⟩
  fin_cases which
  · obtain ⟨v,p,he⟩ := each_lane_arrives hp hw hc 1
    exact ⟨event 1,record 1 v p,he,(pair_source_iff 0 1 value v predicate p).2 (by decide)⟩
  · obtain ⟨v,p,he⟩ := each_lane_arrives hp hw hc 0
    exact ⟨event 0,record 0 v p,he,(pair_source_iff 1 0 value v predicate p).2 (by decide)⟩

theorem actual_control_admitted {launch candidate} (hp : Pre launch)
    (hw : Shuffle.WellFormed Generated.shuffle_pair.program launch candidate) (hc : Shuffle.Complete candidate) :
    ControlAdmitted block candidate := by
  apply control_admitted_of_rank controlRank
  intro left right he
  cases he with
  | «local» => exact Nat.zero_lt_one
  | rendezvous => exact Nat.zero_lt_one
  | po hl hr _ hs =>
    obtain ⟨_,_,_,rfl,_⟩ := actual_event_shape hp hw hc hl
    obtain ⟨_,_,_,rfl,_⟩ := actual_event_shape hp hw hc hr
    exact False.elim (Nat.lt_irrefl 0 hs)
  | exit he _ _ _ =>
    obtain ⟨_,_,_,rfl,rfl⟩ := actual_event_shape hp hw hc he
    exact Nat.lt_succ_self 1
  | exitedPeer he ht _ _ hx =>
    obtain ⟨_,_,_,rfl,rfl⟩ := actual_shuffle_shape hp hw hc he
    obtain ⟨_,_,_,hf,_⟩ := member_source_shape hp hw hc ht
    have hgen := hx.2
    rw [hf] at hgen
    have : 1 ≤ 0 := hgen
    omega
  | barrier hl _ _ =>
    obtain ⟨_,_,_,_,hk⟩ := actual_event_shape hp hw hc hl
    cases hk

theorem source_safe : Shuffle.Safe Generated.shuffle_pair.program Pre := by
  intro launch candidate rf co hp hw hc _ _ _
  rw [hp.1]
  exact actual_defined hp hw hc

theorem actual_reply_correct {launch candidate} (hp : Pre launch)
    (hw : Shuffle.WellFormed Generated.shuffle_pair.program launch candidate) (hc : Shuffle.Complete candidate)
    (ha : Agreement block candidate) (which : Lane2) (value : Nat) (predicate : Bool)
    (he : candidate.shuffleAt (event which) = some (record which value predicate)) :
    wrap 32 value = 1-which.val ∧ predicate = true := by
  fin_cases which
  · obtain ⟨v,p,hpeer⟩ := each_lane_arrives hp hw hc 1
    have ht := ha _ _ he (actual_matched hp hw hc 0 value predicate) _ _ hpeer
      ((pair_source_iff 0 1 value v predicate p).2 (by decide))
    simpa [record,key,event,pair_predicate] using ht
  · obtain ⟨v,p,hpeer⟩ := each_lane_arrives hp hw hc 0
    have ht := ha _ _ he (actual_matched hp hw hc 1 value predicate) _ _ hpeer
      ((pair_source_iff 1 0 value v predicate p).2 (by decide))
    simpa [record,key,event,pair_predicate] using ht

/-- Independent register specification: each lane receives the other lane's
original index and a true selection predicate. -/
def RegisterPost (thread : ThreadId) (state : Shuffle.State) : Prop :=
  ∃ which : Lane2, thread = id which ∧ lookup "%dst" state.base.core.thread.regs = some (1-which.val) ∧
    lookup "%p" state.base.core.thread.regs = some 1

theorem all_completed_registers_correct {launch candidate} (hp : Pre launch)
    (hw : Shuffle.WellFormed Generated.shuffle_pair.program launch candidate) (hc : Shuffle.Complete candidate)
    (ha : Agreement block candidate) : ∀ trace ∈ candidate.traces, RegisterPost trace.id trace.final := by
  intro trace ht
  obtain ⟨which,hi,_,hf,hev⟩ := member_source_shape hp hw hc ht
  have he : candidate.shuffleAt (event which) = some (record which (trace.oracle.shuffle 0).1 (trace.oracle.shuffle 0).2) := by
    unfold Shuffle.Candidate.shuffleAt
    rw [Shuffle.eventAt_of_member hw.2.1 ht (show (event which).thread = trace.id from hi.symm),hev]
    rfl
  obtain ⟨hv,hp⟩ := actual_reply_correct hp hw hc ha which _ _ he
  refine ⟨which,hi,?_,?_⟩ <;> rw [hf]
  · simp [finalState,lookup,put,hv]
  · simp [finalState,lookup,put,hp]

theorem actual_view_empty {launch candidate} (hp : Pre launch)
    (hw : Shuffle.WellFormed Generated.shuffle_pair.program launch candidate) (hc : Shuffle.Complete candidate) :
    ∀ actual, candidate.view.eventAt actual = none := by
  intro actual
  cases he : candidate.view.eventAt actual with
  | none => rfl
  | some kind =>
    obtain ⟨trace,ht,_,hget⟩ := Ptx.Event.eventAt_trace he
    obtain ⟨original,ho,rfl⟩ := List.mem_map.mp ht
    obtain ⟨_,_,_,_,hev⟩ := member_source_shape hp hw hc ho
    change (ordinaryEvents original.events)[actual.serial]? = some kind at hget
    rw [hev] at hget
    simp [ordinaryEvents] at hget

theorem all_completed_memory_frame (domain : List Location) :
    Shuffle.Triple Generated.shuffle_pair.program Pre (fun _ => domain)
      (fun launch output => ∀ loc ∈ domain, output loc = launch.initial loc) := by
  intro launch candidate rf co observation hp hw hc _ _ _ _ ho hd loc hl
  apply Ptx.Event.empty_view_observer_frame (actual_view_empty hp hw hc) ho
  simpa only [hd] using hl

theorem source_nonvacuous (domain : List Location) (hg : ∀ loc ∈ domain, loc.space = .global) :
    Shuffle.Nonvacuous Generated.shuffle_pair.program Pre (fun _ => domain) := by
  intro actualLaunch hp
  rcases actualLaunch with ⟨geometry,params,initial⟩
  rcases hp with ⟨rfl,rfl⟩
  let c := candidate 1 0 true true
  let rf : Ptx.Event.ReadsFrom := fun _ _ => .initial
  have hw := actual_source_well_formed 1 0 true true initial
  have hc := actual_source_complete 1 0 true true
  have hp : Pre (launch initial) := ⟨rfl,rfl⟩
  have he := actual_view_empty hp hw hc
  exact ⟨c,rf,Ptx.Event.InitialCo c.view,⟨domain,initial,fun _ => .initial⟩,hw,hc,
    pair_control_admitted 1 0 true true,pair_defined 1 0 true true,(pair_agreement_iff 1 0 true true).2 (by decide),
    Ptx.Event.empty_view_memory_conditions initial rf he,
    Ptx.Event.empty_view_observer initial rf domain he (Shuffle.view_complete hc) hg,rfl⟩

end
end Ptx.Kernels.ShufflePair
