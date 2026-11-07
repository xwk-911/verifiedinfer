import Ptx.Kernels.BarrierPublish

namespace Ptx.BarrierPublishTests
open Ptx Ptx.ISA Ptx.Event
open Ptx.BarrierPublish

theorem incorrect_consumer_rejected (base : Nat) (initial : ByteMap)
    (sources : ReadsFrom) (order : Coherence) :
    ¬ GenericMemoryConditions (graph base 1 0) initial sources order := by
  intro hc
  exact (show wrap 32 0 ≠ wrap 32 1 by decide) (family_output_correct hc)

theorem incorrect_observer_rejected {base initial sources order o}
    (hc : GenericMemoryConditions (graph base 1 1) initial sources order)
    (hd : o.domain = wordDomain base) (hz : observedU32 o base = 0) :
    ¬ ObserverConditions (graph base 1 1) initial sources order o := by
  intro ho
  have hv := observed_word_correct hc ho hd
  rw [hz] at hv
  exact (show (0 : Nat) ≠ wrap 32 1 by decide) hv

/-- Reject a stale SOURCE even if initialization happens to have the same value
as the store. Comparing just the observed value would miss this distinction. -/
theorem initial_observer_source_rejected {base value initial sources order o}
    (hc : GenericMemoryConditions (graph base value value) initial sources order)
    (hd : o.domain = wordDomain base) (hs : o.source ((loc base).add 0) = .initial) :
    ¬ ObserverConditions (graph base value value) initial sources order o := by
  intro ho
  have he := race_free_observer_eligible (no_races base value value sources) ((loc base).add 0)
  have hmem : (loc base).add 0 ∈ o.domain := by
    rw [hd]
    exact List.mem_map.mpr ⟨0, by decide, rfl⟩
  have hw : (graph base value value).writeByte w ((loc base).add 0) =
      some ((bytes value)[0]'(by simp [bytes])) := by
    change payloadByte (loc base) (bytes value) ((loc base).add 0) = _
    rw [payloadByte_offset]
    rfl
  apply ho.noStale _ hmem he.1 w _ hw
  rw [hs]
  exact (hc.coherence he.1).initialization _ w _ hw

theorem frame_observation (value : Nat) (initial : ByteMap) :
    let c := graph 0 value value
    let o := singleWriterObservation c initial w (wordDomain 0 ++ [(loc 0).add 4])
    ObserverConditions c initial rf (InitialCo c) o ∧ o.output ((loc 0).add 4) = initial ((loc 0).add 4) := by
  dsimp only
  constructor
  · apply single_writer_observation (complete 0 value value)
    · intro address hmem
      simp only [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with h | rfl
      · exact wordDomain_global 0 address h
      · rfl
    · exact fun _ _ _ h => (write_shape h).1
  · change (payloadByte (loc 0) (bytes value) ((loc 0).add 4)).getD _ = _
    rw [payloadByte_offset]
    rfl

theorem concrete_observed_value :
    observedU32 (singleWriterObservation (graph 16 0x12345678 0x12345678)
      (fun _ => byte 0) w (wordDomain 16)) 16 = 0x12345678 := by decide

end Ptx.BarrierPublishTests
