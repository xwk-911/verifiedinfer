import Ptx.Kernels.AtomicDispatchLayout

/-! Bytewise sources and ticket uniqueness for arbitrary complete candidates.
No assignment of jobs to CTAs, uniform reads-from source, no-race property or
inter-CTA relaxed causality is added to the launch precondition. -/
namespace Ptx.AtomicDispatchEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.AtomicDispatchTrace
noncomputable section

theorem ordered_tickets (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    {rf : ReadsFrom} {co : Coherence} {first second : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    (hi : Initialized cfg launch.initial) (hm : GenericMemoryConditions execution launch.initial rf co)
    (hf : first ∈ execution.traces) (hs : second ∈ execution.traces)
    (hcover : ∀ offset, offset < 4 → ∀ writer value,
      execution.writeByte writer ((counterLoc cfg).add offset) = some value →
      writer = ⟨first.id,0⟩ ∨ writer = ⟨second.id,0⟩)
    (hc : co (counterLoc cfg) (.write ⟨first.id,0⟩) (.write ⟨second.id,0⟩)) :
    ticket first.oracle = 0 ∧ ticket second.oracle = 1 := by
  let a : EventId := ⟨first.id,0⟩
  let b : EventId := ⟨second.id,0⟩
  have ha := counter_event cfg hw hd hp hf
  have hb := counter_event cfg hw hd hp hs
  have hstrong : MorallyStrong execution a b := rmw_morally_strong ha hb (by simp [atomicAddBytes]) True.intro True.intro
  have hnomixed := no_mixed cfg hw hd hg hp rf
  have hwa0 := counter_write_byte cfg hw hd hp hf (offset := 0) (by decide)
  have hwb0 := counter_write_byte cfg hw hd hp hs (offset := 0) (by decide)
  simp only [Location.add,Nat.add_zero] at hwa0 hwb0
  have hfirst : ticket first.oracle = 0 := by
    apply u32_bytes_injective (ticket_bound _) (by decide)
    intro offset ho
    have hr := counter_read_byte cfg hw hd hp hf ho
    have hwa := counter_write_byte cfg hw hd hp hf ho
    have hwb := counter_write_byte cfg hw hd hp hs ho
    have helig := counter_eligible cfg hw hd hg hp rf (counter_offset cfg ho) (Or.inl (by rw [hr]; rfl))
    cases hrf : rf a ((counterLoc cfg).add offset) with
    | initial => exact (initial_read_value hm.agreement helig hr hrf).trans (hi offset ho)
    | write writer =>
      have hv := write_read_value hm.agreement helig hr hrf
      rcases hcover offset ho writer _ hv with he | he
      · subst writer
        exact (rmw_no_self_read hm hnomixed hr hwa hrf).elim
      · subst writer
        exact (coherence_before_cannot_read_after hm hnomixed hstrong hwa0 hwb0 hc hr hwb hrf).elim
  refine ⟨hfirst,?_⟩
  apply u32_bytes_injective (ticket_bound _) (by decide)
  intro offset ho
  have hr := counter_read_byte cfg hw hd hp hs ho
  have hwa := counter_write_byte cfg hw hd hp hf ho
  have hwb := counter_write_byte cfg hw hd hp hs ho
  have helig := counter_eligible cfg hw hd hg hp rf (counter_offset cfg ho) (Or.inl (by rw [hr]; rfl))
  cases hrf : rf b ((counterLoc cfg).add offset) with
  | initial =>
    have his : execution.IsRMW b := ⟨.gpu,counterLoc cfg,atomicAddBytes (reply second.oracle) 1,hb⟩
    exact (rmw_predecessor_excludes_initial_any_byte hm hnomixed his (morally_strong_symmetric hstrong)
      hr hwa hwb0 hwa0 hc hrf).elim
  | write writer =>
    have hv := write_read_value hm.agreement helig hr hrf
    rcases hcover offset ho writer _ hv with he | he
    · subst writer
      have heq := Option.some.inj (hv.symm.trans hwa)
      simpa only [hfirst,show wrap 32 (0+1) = 1 from rfl] using heq
    · subst writer
      exact (rmw_no_self_read hm hnomixed hr hwb hrf).elim

theorem tickets (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    {rf : ReadsFrom} {co : Coherence} {t0 t1 : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    (hi : Initialized cfg launch.initial) (hm : GenericMemoryConditions execution launch.initial rf co)
    (h0 : t0 ∈ execution.traces) (h1 : t1 ∈ execution.traces) (hid0 : t0.id = id 0) (hid1 : t1.id = id 1) :
    (ticket t0.oracle = 0 ∧ ticket t1.oracle = 1) ∨ (ticket t0.oracle = 1 ∧ ticket t1.oracle = 0) := by
  have ha := counter_event cfg hw hd hp h0
  have hb := counter_event cfg hw hd hp h1
  have hstrong := rmw_morally_strong ha hb (by simp [atomicAddBytes]) True.intro True.intro
  have hwa := counter_write_byte cfg hw hd hp h0 (offset := 0) (by decide)
  have hwb := counter_write_byte cfg hw hd hp h1 (offset := 0) (by decide)
  simp only [Location.add,Nat.add_zero] at hwa hwb
  have hne : (⟨t0.id,0⟩ : EventId) ≠ ⟨t1.id,0⟩ := by simp [hid0,hid1,id]
  have hcover : ∀ offset, offset < 4 → ∀ writer value,
      execution.writeByte writer ((counterLoc cfg).add offset) = some value →
      writer = ⟨t0.id,0⟩ ∨ writer = ⟨t1.id,0⟩ := by
    intro offset ho writer value hwri
    have hi := counter_write_ids cfg hw hd hg hp (counter_offset cfg ho) hwri
    simpa only [counterId,hid0,hid1] using hi
  rcases (hm.coherence (no_mixed cfg hw hd hg hp rf)).comparable (counterLoc cfg) _ _ _ _ hne hwa hwb (Or.inl hstrong) with hc | hc
  · exact Or.inl (ordered_tickets cfg hw hd hg hp hi hm h0 h1 hcover hc)
  · have hs := ordered_tickets cfg hw hd hg hp hi hm h1 h0 (by
      intro offset ho writer value hwri
      exact (hcover offset ho writer value hwri).symm) hc
    exact Or.inr ⟨hs.2,hs.1⟩

end
end Ptx.AtomicDispatchEvent
