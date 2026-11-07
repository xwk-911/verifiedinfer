import Ptx.Kernels.ReleaseAcquireMessageUniversalMemory

/-! Universal completed-execution contract for the mechanical PTX translation.
The flag must initially represent zero. Source oracles, finite polling counts,
trace order, reads-from, coherence and final observers remain universally
quantified. Termination/fairness and physical runtime interpretation are separate.
-/
namespace Ptx.Kernels.ReleaseAcquireMessage
open Ptx.ISA
noncomputable section

def Pre (actualLaunch : Scalar.Launch) : Prop :=
  SourcePre actualLaunch ∧ Scalar.RepresentsU32 actualLaunch.initial flag 0

namespace CompletedShape
variable {execution : Ordered.Candidate} {retries flagValue payloadValue : Nat}

theorem view_payload_write (hs : CompletedShape execution retries flagValue payloadValue) :
    execution.view.eventAt payloadWrite = some (.write payload (Scalar.u32Bytes 42)) := by
  rw [Ordered.view_eventAt,hs.payload_write]; rfl

theorem view_flag_write (hs : CompletedShape execution retries flagValue payloadValue) :
    execution.view.eventAt flagWrite = some (.write flag (Scalar.u32Bytes 1)) := by
  rw [Ordered.view_eventAt,hs.flag_write]; rfl

theorem view_last_acquire (hs : CompletedShape execution retries flagValue payloadValue) :
    execution.view.eventAt (finalFlagRead retries) = some (.read flag (Scalar.u32Bytes (word flagValue))) := by
  rw [Ordered.view_eventAt,hs.last_acquire]; rfl

theorem view_payload_read (hs : CompletedShape execution retries flagValue payloadValue) :
    execution.view.eventAt (finalPayloadRead retries) = some (.read payload (Scalar.u32Bytes (word payloadValue))) := by
  rw [Ordered.view_eventAt,hs.payload_read]; rfl

theorem view_output_write (hs : CompletedShape execution retries flagValue payloadValue) :
    execution.view.eventAt (finalOutputWrite retries) = some (.write output (Scalar.u32Bytes (word payloadValue))) := by
  rw [Ordered.view_eventAt,hs.output_write]; rfl

theorem unique_word_writer (hs : CompletedShape execution retries flagValue payloadValue) {writer base value}
    (hw : execution.view.eventAt writer = some (.write base (Scalar.u32Bytes value)))
    {offset : Nat} (ho : offset < 4) {other v}
    (hother : execution.view.writeByte other (base.add offset) = some v) : other = writer := by
  have hown : execution.view.writeByte writer (base.add offset) = some (Scalar.u32Byte value offset) := by
    simpa only [Ptx.Event.Candidate.writeByte,hw,Option.bind_some,Ptx.Event.Kind.writeByte]
      using Scalar.u32_payload_byte base value offset ho
  exact hs.unique_byte_writer hother hown

theorem flag_read_eligible (hs : CompletedShape execution retries flagValue payloadValue) (sources : Ptx.Event.ReadsFrom)
    {offset : Nat} (ho : offset < 4) : Ordered.Eligible execution sources (finalFlagRead retries) (flag.add offset) :=
  Ordered.unique_writer_strong_read_eligible (hs.no_mixed_size_races sources)
    (fun _ _ hw => hs.unique_word_writer hs.view_flag_write ho hw) (Ordered.morally_strong_symm hs.flag_strong)

theorem final_flag_synchronizes (hs : CompletedShape execution retries flagValue payloadValue) {initial sources co}
    (hm : Ordered.MemoryConditions execution initial sources co) (hi : Scalar.RepresentsU32 initial flag 0) :
    Ordered.ReleaseAcquireSync execution sources flagWrite (finalFlagRead retries) := by
  have hv : word flagValue < 2^32 := by
    unfold word wrap
    exact Nat.mod_lt _ (by decide)
  apply Ordered.release_acquire_of_nonzero_u32 hm hs.view_last_acquire
    (fun _ ho => hs.flag_read_eligible sources ho) hi hv hs.nonzero
    (fun _ ho _ _ hw => hs.unique_word_writer hs.view_flag_write ho hw)
  · rw [hs.flag_write]; rfl
  · rw [hs.last_acquire]; rfl
  · exact hs.flag_strong

theorem payload_before_release (hs : CompletedShape execution retries flagValue payloadValue) :
    Ptx.Event.ProgramOrder execution.view payloadWrite flagWrite :=
  ⟨by rw [Ptx.Event.Candidate.Present,hs.view_payload_write]; rfl,
    by rw [Ptx.Event.Candidate.Present,hs.view_flag_write]; rfl,rfl,by decide⟩

theorem acquire_before_payload (hs : CompletedShape execution retries flagValue payloadValue) :
    Ptx.Event.ProgramOrder execution.view (finalFlagRead retries) (finalPayloadRead retries) :=
  ⟨by rw [Ptx.Event.Candidate.Present,hs.view_last_acquire]; rfl,
    by rw [Ptx.Event.Candidate.Present,hs.view_payload_read]; rfl,rfl,by simp [finalFlagRead,finalPayloadRead]⟩

theorem payload_causal (hs : CompletedShape execution retries flagValue payloadValue) {initial sources co}
    (hm : Ordered.MemoryConditions execution initial sources co) (hi : Scalar.RepresentsU32 initial flag 0) :
    Ordered.Causality execution sources payloadWrite (finalPayloadRead retries) := by
  refine Or.inl ⟨?_,Ordered.publish_release_acquire hs.payload_before_release (hs.final_flag_synchronizes hm hi) hs.acquire_before_payload⟩
  refine ⟨payload.add 0,Or.inr ?_,Or.inl ?_⟩
  · simp only [Ptx.Event.Candidate.writeByte,hs.view_payload_write,Option.bind_some,Ptx.Event.Kind.writeByte]
    rw [Scalar.u32_payload_byte payload 42 0 (by decide)]; rfl
  · simp only [Ptx.Event.Candidate.readByte,hs.view_payload_read,Option.bind_some,Ptx.Event.Kind.readByte]
    rw [Scalar.u32_payload_byte payload (word payloadValue) 0 (by decide)]; rfl

theorem payload_value (hs : CompletedShape execution retries flagValue payloadValue) {initial sources co}
    (hm : Ordered.MemoryConditions execution initial sources co) (hi : Scalar.RepresentsU32 initial flag 0) :
    word payloadValue = 42 := by
  apply Scalar.u32_bytes_injective
  · unfold word wrap; exact Nat.mod_lt _ (by decide)
  · decide
  · intro offset ho
    have hc := hs.payload_causal hm hi
    have he := Ordered.unique_writer_causal_read_eligible (hs.no_mixed_size_races sources)
      (fun _ _ hw => hs.unique_word_writer hs.view_payload_write ho hw) hc
    have hr : execution.view.readByte (finalPayloadRead retries) (payload.add offset) = some (Scalar.u32Byte (word payloadValue) offset) := by
      simpa only [Ptx.Event.Candidate.readByte,hs.view_payload_read,Option.bind_some,Ptx.Event.Kind.readByte]
        using Scalar.u32_payload_byte payload (word payloadValue) offset ho
    have hw : execution.view.writeByte payloadWrite (payload.add offset) = some (Scalar.u32Byte 42 offset) := by
      simpa only [Ptx.Event.Candidate.writeByte,hs.view_payload_write,Option.bind_some,Ptx.Event.Kind.writeByte]
        using Scalar.u32_payload_byte payload 42 offset ho
    exact Ordered.causal_read_unique_writer hm he hr hw hc (fun _ _ hh => hs.unique_word_writer hs.view_payload_write ho hh)

theorem observed_post (hs : CompletedShape execution retries flagValue payloadValue) {initial sources co observation}
    (hm : Ordered.MemoryConditions execution initial sources co) (hi : Scalar.RepresentsU32 initial flag 0)
    (ho : Ordered.ObserverConditions execution initial sources co observation) (hd : observation.domain = domain) :
    Post initial observation.output := by
  have hu : ∀ writer base value, execution.view.eventAt writer = some (.write base (Scalar.u32Bytes value)) →
      (base = payload ∨ base = flag ∨ base = output) → Scalar.RepresentsU32 observation.output base value := by
    intro writer base value hw hb
    apply Ordered.observe_u32_write hm ho hw
    · intro offset hoffset
      rw [hd]
      exact domain_covers_words hb hoffset
    · exact fun _ _ => hs.observer_eligible sources _
    · exact fun _ hoffset _ _ hother => hs.unique_word_writer hw hoffset hother
  have hout : execution.view.eventAt (finalOutputWrite retries) = some (.write output (Scalar.u32Bytes 42)) := by
    rw [hs.view_output_write,hs.payload_value hm hi]
  refine ⟨hu payloadWrite payload 42 hs.view_payload_write (Or.inl rfl),
    hu flagWrite flag 1 hs.view_flag_write (Or.inr (Or.inl rfl)),
    hu (finalOutputWrite retries) output 42 hout (Or.inr (Or.inr rfl)),?_⟩
  intro loc hl houtside
  apply Ordered.observer_unwritten ho _ (hs.observer_eligible sources loc) (hs.outside_written_has_no_writer houtside)
  simpa only [hd] using hl

end CompletedShape

theorem correct : Ordered.Triple code Pre (fun _ => domain) (fun actualLaunch final => Post actualLaunch.initial final) := by
  intro actualLaunch execution sources co observation hp hw hc hm ho hd
  obtain ⟨retries,flagValue,payloadValue,hs⟩ := completed_shape hp.1 hw hc
  exact hs.observed_post hm hp.2 ho hd

theorem initialized_nonvacuous : Ordered.Nonvacuous code Pre (fun _ => domain) :=
  fun actualLaunch hp => nonvacuous actualLaunch hp.1

theorem correct_and_nonvacuous :
    Ordered.Triple code Pre (fun _ => domain) (fun actualLaunch final => Post actualLaunch.initial final) ∧
    Ordered.Nonvacuous code Pre (fun _ => domain) := ⟨correct,initialized_nonvacuous⟩

end
end Ptx.Kernels.ReleaseAcquireMessage
