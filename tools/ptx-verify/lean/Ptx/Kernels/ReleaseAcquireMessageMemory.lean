import Ptx.Kernels.ReleaseAcquireMessageGraph

/-! Constructed scoped memory consistency for the SAME complete source
candidate, using actual byte values and unique writers. This is a witness,
not the arbitrary-completed-source functional correctness theorem. -/
namespace Ptx.Kernels.ReleaseAcquireMessage
open Ptx.ISA
noncomputable section

theorem write_cases {event loc value} (hw : candidate.view.writeByte event loc = some value) :
    (event = payloadWrite ∧ Ptx.Event.payloadByte payload (Scalar.u32Bytes 42) loc = some value) ∨
    (event = flagWrite ∧ Ptx.Event.payloadByte flag (Scalar.u32Bytes 1) loc = some value) ∨
    (event = outputWrite ∧ Ptx.Event.payloadByte output (Scalar.u32Bytes 42) loc = some value) := by
  obtain ⟨kind,hkind⟩ := Option.isSome_iff_exists.mp (Ptx.Event.accesses_present (Or.inr (by rw [hw]; rfl)))
  obtain ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ := view_event_cases hkind
  · exact Or.inl ⟨rfl,by simpa only [Ptx.Event.Candidate.writeByte,hkind,Option.bind_some,Ptx.Event.Kind.writeByte] using hw⟩
  · exact Or.inr (Or.inl ⟨rfl,by simpa only [Ptx.Event.Candidate.writeByte,hkind,Option.bind_some,Ptx.Event.Kind.writeByte] using hw⟩)
  · simp only [Ptx.Event.Candidate.writeByte,hkind,Option.bind_some,Ptx.Event.Kind.writeByte,reduceCtorEq] at hw
  · simp only [Ptx.Event.Candidate.writeByte,hkind,Option.bind_some,Ptx.Event.Kind.writeByte,reduceCtorEq] at hw
  · exact Or.inr (Or.inr ⟨rfl,by simpa only [Ptx.Event.Candidate.writeByte,hkind,Option.bind_some,Ptx.Event.Kind.writeByte] using hw⟩)

theorem read_cases {event loc value} (hr : candidate.view.readByte event loc = some value) :
    (event = flagRead ∧ Ptx.Event.payloadByte flag (Scalar.u32Bytes 1) loc = some value) ∨
    (event = payloadRead ∧ Ptx.Event.payloadByte payload (Scalar.u32Bytes 42) loc = some value) := by
  obtain ⟨kind,hkind⟩ := Option.isSome_iff_exists.mp (Ptx.Event.accesses_present (Or.inl (by rw [hr]; rfl)))
  obtain ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ := view_event_cases hkind
  · simp only [Ptx.Event.Candidate.readByte,hkind,Option.bind_some,Ptx.Event.Kind.readByte,reduceCtorEq] at hr
  · simp only [Ptx.Event.Candidate.readByte,hkind,Option.bind_some,Ptx.Event.Kind.readByte,reduceCtorEq] at hr
  · exact Or.inl ⟨rfl,by simpa only [Ptx.Event.Candidate.readByte,hkind,Option.bind_some,Ptx.Event.Kind.readByte] using hr⟩
  · exact Or.inr ⟨rfl,by simpa only [Ptx.Event.Candidate.readByte,hkind,Option.bind_some,Ptx.Event.Kind.readByte] using hr⟩
  · simp only [Ptx.Event.Candidate.readByte,hkind,Option.bind_some,Ptx.Event.Kind.readByte,reduceCtorEq] at hr

theorem unique_byte_writer {loc a b va vb} (ha : candidate.view.writeByte a loc = some va)
    (hb : candidate.view.writeByte b loc = some vb) : a = b := by
  obtain ⟨rfl,hva⟩ | ⟨rfl,hva⟩ | ⟨rfl,hva⟩ := write_cases ha
  all_goals obtain ⟨rfl,hvb⟩ | ⟨rfl,hvb⟩ | ⟨rfl,hvb⟩ := write_cases hb
  all_goals try rfl
  all_goals
    have hba := Ptx.Event.payloadByte_bounds hva
    have hbb := Ptx.Event.payloadByte_bounds hvb
    simp only [payload,flag,output,Scalar.u32_bytes_size] at hba hbb
    omega

theorem rf_flag (loc : Location) : rf flagRead loc = .write flagWrite := rfl
theorem rf_payload (loc : Location) : rf payloadRead loc = .write payloadWrite := rfl

theorem actual_read_values_match (initial : Scalar.ByteMap) {read loc value}
    (hr : candidate.view.readByte read loc = some value) :
    Ptx.Event.sourceByte candidate.view initial loc (rf read loc) = some value := by
  obtain ⟨rfl,hbyte⟩ | ⟨rfl,hbyte⟩ := read_cases hr
  · rw [rf_flag]
    have he : candidate.view.eventAt flagWrite = some (.write flag (Scalar.u32Bytes 1)) := rfl
    simpa only [Ptx.Event.sourceByte,Ptx.Event.Candidate.writeByte,he,Option.bind_some,Ptx.Event.Kind.writeByte] using hbyte
  · rw [rf_payload]
    have he : candidate.view.eventAt payloadWrite = some (.write payload (Scalar.u32Bytes 42)) := rfl
    simpa only [Ptx.Event.sourceByte,Ptx.Event.Candidate.writeByte,he,Option.bind_some,Ptx.Event.Kind.writeByte] using hbyte

theorem reads_from_rank {read writer loc vr vw} (hr : candidate.view.readByte read loc = some vr)
    (_hw : candidate.view.writeByte writer loc = some vw) (hs : rf read loc = .write writer) : rank writer < rank read := by
  obtain ⟨rfl,_⟩ | ⟨rfl,_⟩ := read_cases hr
  · rw [rf_flag] at hs
    have hi := Ptx.Event.Source.write.inj hs
    subst writer
    decide
  · rw [rf_payload] at hs
    have hi := Ptx.Event.Source.write.inj hs
    subst writer
    decide

theorem reads_from_initial_impossible {read loc value} (hr : candidate.view.readByte read loc = some value) :
    rf read loc ≠ .initial := by
  obtain ⟨rfl,_⟩ | ⟨rfl,_⟩ := read_cases hr
  · rw [rf_flag]; intro h; cases h
  · rw [rf_payload]; intro h; cases h

theorem actual_memory_consistent (initial : Scalar.ByteMap) :
    Ordered.MemoryConditions candidate initial rf (Ptx.Event.InitialCo candidate.view) := by
  apply Ordered.initial_co_conditions rank
  · exact fun _ _ hp => program_order_rank hp
  · rintro a b ⟨_,bid,generation,_,hret⟩
    exact False.elim (no_barrier_returns hret)
  · exact fun _ _ hs => release_acquire_rank hs
  · rintro a b ⟨_,_,_,_,_,bid,generation,hret,_⟩
    exact False.elim (no_barrier_returns hret)
  · intro event bid generation hret
    exact False.elim (no_barrier_returns hret)
  · exact fun _ _ _ _ _ ha hb => unique_byte_writer ha hb
  · exact fun _ _ _ hr => actual_read_values_match initial hr
  · exact fun _ _ _ _ _ hr hw hs => reads_from_rank hr hw hs
  · intro read writer loc vr vw hr _ hs
    exact False.elim (reads_from_initial_impossible hr hs)

theorem complete_source_and_memory_witness :
    Ordered.WellFormed code launch candidate ∧ Ordered.Complete candidate ∧
    Ordered.MemoryConditions candidate launch.initial rf (Ptx.Event.InitialCo candidate.view) :=
  ⟨source_candidate_is_well_formed,source_candidate_is_complete,actual_memory_consistent launch.initial⟩

end
end Ptx.Kernels.ReleaseAcquireMessage
