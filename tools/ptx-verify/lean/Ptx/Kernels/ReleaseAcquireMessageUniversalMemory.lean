import Ptx.Kernels.ReleaseAcquireMessageUniversalGraph
import Ptx.Ordered.ReadRules

/-! Byte layout and scope facts derived from all completed source candidates.
Repeated polling changes read-event indices but never invents another writer.
No reads-from or coherence choice is fixed by these source facts. -/
namespace Ptx.Kernels.ReleaseAcquireMessage.CompletedShape
open Ptx.ISA
noncomputable section
variable {execution : Ordered.Candidate} {retries flagValue payloadValue : Nat}

theorem write_cases (hs : CompletedShape execution retries flagValue payloadValue) {event loc value}
    (hw : execution.view.writeByte event loc = some value) :
    (event = payloadWrite ∧ Ptx.Event.payloadByte payload (Scalar.u32Bytes 42) loc = some value) ∨
    (event = flagWrite ∧ Ptx.Event.payloadByte flag (Scalar.u32Bytes 1) loc = some value) ∨
    (event = finalOutputWrite retries ∧ Ptx.Event.payloadByte output (Scalar.u32Bytes (word payloadValue)) loc = some value) := by
  obtain ⟨kind,hkind⟩ := Option.isSome_iff_exists.mp (Ptx.Event.accesses_present (Or.inr (by rw [hw]; rfl)))
  obtain ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨_,_,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ := hs.view_cases hkind
  · exact Or.inl ⟨rfl,by simpa only [Ptx.Event.Candidate.writeByte,hkind,Option.bind_some,Ptx.Event.Kind.writeByte] using hw⟩
  · exact Or.inr (Or.inl ⟨rfl,by simpa only [Ptx.Event.Candidate.writeByte,hkind,Option.bind_some,Ptx.Event.Kind.writeByte] using hw⟩)
  · simp only [Ptx.Event.Candidate.writeByte,hkind,Option.bind_some,Ptx.Event.Kind.writeByte,reduceCtorEq] at hw
  · simp only [Ptx.Event.Candidate.writeByte,hkind,Option.bind_some,Ptx.Event.Kind.writeByte,reduceCtorEq] at hw
  · exact Or.inr (Or.inr ⟨rfl,by simpa only [Ptx.Event.Candidate.writeByte,hkind,Option.bind_some,Ptx.Event.Kind.writeByte] using hw⟩)

theorem unique_byte_writer (hs : CompletedShape execution retries flagValue payloadValue) {loc a b va vb}
    (ha : execution.view.writeByte a loc = some va) (hb : execution.view.writeByte b loc = some vb) : a = b := by
  obtain ⟨rfl,hva⟩ | ⟨rfl,hva⟩ | ⟨rfl,hva⟩ := hs.write_cases ha
  all_goals obtain ⟨rfl,hvb⟩ | ⟨rfl,hvb⟩ | ⟨rfl,hvb⟩ := hs.write_cases hb
  all_goals try rfl
  all_goals
    have hba := Ptx.Event.payloadByte_bounds hva
    have hbb := Ptx.Event.payloadByte_bounds hvb
    simp only [payload,flag,output,Scalar.u32_bytes_size] at hba hbb
    omega

theorem word_footprint (hs : CompletedShape execution retries flagValue payloadValue) {event}
    (he : execution.view.Present event) :
    ∃ base, (execution.view.eventAt event).bind Ptx.Event.Kind.footprint = some (base,4) ∧ base.address % 4 = 0 := by
  obtain ⟨kind,hkind⟩ := Option.isSome_iff_exists.mp he
  obtain ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨_,_,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ := hs.view_cases hkind
  · exact ⟨payload,by simp only [hkind,Option.bind_some,Ptx.Event.Kind.footprint,Scalar.u32_bytes_size],by decide⟩
  · exact ⟨flag,by simp only [hkind,Option.bind_some,Ptx.Event.Kind.footprint,Scalar.u32_bytes_size],by decide⟩
  · exact ⟨flag,by simp only [hkind,Option.bind_some,Ptx.Event.Kind.footprint,Scalar.u32_bytes_size],by decide⟩
  · exact ⟨payload,by simp only [hkind,Option.bind_some,Ptx.Event.Kind.footprint,Scalar.u32_bytes_size],by decide⟩
  · exact ⟨output,by simp only [hkind,Option.bind_some,Ptx.Event.Kind.footprint,Scalar.u32_bytes_size],by decide⟩

theorem no_mixed_size_races (hs : CompletedShape execution retries flagValue payloadValue) (sources : Ptx.Event.ReadsFrom) :
    ¬Ordered.MixedSizeRace execution sources := by
  rintro ⟨a,b,hr,hn⟩
  obtain ⟨_,ha,hb⟩ := hr.overlap
  obtain ⟨base,hbase,halign⟩ := hs.word_footprint (Ptx.Event.accesses_present ha)
  obtain ⟨other,hother,hbalign⟩ := hs.word_footprint (Ptx.Event.accesses_present hb)
  have he := Ptx.Event.overlapping_aligned_words_same_base hbase hother halign hbalign hr.overlap
  exact hn ⟨(base,4),hbase,he ▸ hother⟩

theorem observer_eligible (hs : CompletedShape execution retries flagValue payloadValue) (sources : Ptx.Event.ReadsFrom) (loc : Location) :
    Ordered.ObserverEligible execution sources loc :=
  Ordered.unique_byte_observer_eligible (hs.no_mixed_size_races sources) (fun _ _ _ _ ha hb => hs.unique_byte_writer ha hb)

theorem outside_written_has_no_writer (hs : CompletedShape execution retries flagValue payloadValue) {loc}
    (hout : ¬Written loc) : ∀ writer, execution.view.writeByte writer loc = none := by
  intro writer
  cases hw : execution.view.writeByte writer loc with
  | none => rfl
  | some value =>
    obtain ⟨_,hbyte⟩ | ⟨_,hbyte⟩ | ⟨_,hbyte⟩ := hs.write_cases hw
    all_goals
      have hb := Ptx.Event.payloadByte_bounds hbyte
      simp only [payload,flag,output,Scalar.u32_bytes_size] at hb
      exact False.elim (hout ⟨hb.1.symm,by omega⟩)

theorem flag_strong (hs : CompletedShape execution retries flagValue payloadValue) :
    Ordered.MorallyStrong execution flagWrite (finalFlagRead retries) := by
  refine ⟨Or.inr ⟨.gpu,.gpu,?_,?_,by trivial,by trivial⟩,?_⟩
  · rw [hs.flag_write]; rfl
  · rw [hs.last_acquire]; rfl
  · refine ⟨(flag,4),?_,?_⟩
    · rw [Ordered.view_eventAt,hs.flag_write]; rfl
    · rw [Ordered.view_eventAt,hs.last_acquire]; rfl

end
end Ptx.Kernels.ReleaseAcquireMessage.CompletedShape
