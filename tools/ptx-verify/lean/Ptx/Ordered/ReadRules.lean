import Ptx.Ordered.Observation

/-! Scoped read eligibility and publication flags. These are reusable local
rules derived from the fixed predicates; none assumes a particular program,
canonical execution, functional postcondition or termination property. -/
namespace Ptx.Ordered
open Ptx.ISA Ptx.Event
noncomputable section

theorem write_self_strong {candidate event loc value} (hw : candidate.view.writeByte event loc = some value) :
    MorallyStrong candidate event event := ⟨Or.inl rfl,(Ptx.Event.write_self_strong hw).2⟩

theorem morally_strong_symm {candidate a b} (hm : MorallyStrong candidate a b) : MorallyStrong candidate b a := by
  refine ⟨?_,?_⟩
  · rcases hm.1 with he | ⟨sa,sb,hsa,hsb,ha,hb⟩
    · exact Or.inl he.symm
    · exact Or.inr ⟨sb,sa,hsb,hsa,hb,ha⟩
  · obtain ⟨footprint,ha,hb⟩ := hm.2
    exact ⟨footprint,hb,ha⟩

theorem unique_writer_strong_read_eligible {candidate rf read writer loc}
    (hn : ¬MixedSizeRace candidate rf)
    (hu : ∀ other value, candidate.view.writeByte other loc = some value → other = writer)
    (hs : MorallyStrong candidate read writer) : Eligible candidate rf read loc := by
  refine ⟨hn,?_⟩
  rintro (⟨other,hw,hrace⟩ | ⟨a,b,ha,hb,hrace⟩)
  · obtain ⟨value,hvalue⟩ := Option.isSome_iff_exists.mp hw
    have hi := hu other value hvalue
    subst other
    exact hrace.notStrong hs
  · obtain ⟨va,hva⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨vb,hvb⟩ := Option.isSome_iff_exists.mp hb
    have hia := hu a va hva
    have hib := hu b vb hvb
    subst a; subst b
    exact hrace.notStrong (write_self_strong hva)

theorem unique_writer_causal_read_eligible {candidate rf read writer loc}
    (hn : ¬MixedSizeRace candidate rf)
    (hu : ∀ other value, candidate.view.writeByte other loc = some value → other = writer)
    (hc : Causality candidate rf writer read) : Eligible candidate rf read loc := by
  refine ⟨hn,?_⟩
  rintro (⟨other,hw,hrace⟩ | ⟨a,b,ha,hb,hrace⟩)
  · obtain ⟨value,hvalue⟩ := Option.isSome_iff_exists.mp hw
    have hi := hu other value hvalue
    subst other
    exact hrace.notBackward hc
  · obtain ⟨va,hva⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨vb,hvb⟩ := Option.isSome_iff_exists.mp hb
    have hia := hu a va hva
    have hib := hu b vb hvb
    subst a; subst b
    exact hrace.notStrong (write_self_strong hva)

theorem nonzero_u32_read_observes_writer {candidate initial rf co read writer base value}
    (hm : MemoryConditions candidate initial rf co)
    (hr : candidate.view.eventAt read = some (.read base (Scalar.u32Bytes value)))
    (he : ∀ offset, offset < 4 → Eligible candidate rf read (base.add offset))
    (hi : Scalar.RepresentsU32 initial base 0) (hv : value < 2^32) (hn : value ≠ 0)
    (hu : ∀ offset, offset < 4 → ∀ other v, candidate.view.writeByte other (base.add offset) = some v → other = writer) :
    ∃ offset, offset < 4 ∧ rf read (base.add offset) = .write writer := by
  classical
  by_contra hmissing
  have hbytes : ∀ offset, offset < 4 → Scalar.u32Byte value offset = Scalar.u32Byte 0 offset := by
    intro offset hoffset
    have hread : candidate.view.readByte read (base.add offset) = some (Scalar.u32Byte value offset) := by
      simpa only [Ptx.Event.Candidate.readByte,hr,Option.bind_some,Ptx.Event.Kind.readByte]
        using Scalar.u32_payload_byte base value offset hoffset
    have ha := hm.agreement read (base.add offset) _ (he offset hoffset) hread
    cases hs : rf read (base.add offset) with
    | initial =>
      have ha' : some (initial (base.add offset)) = some (Scalar.u32Byte value offset) := by simpa [hs,sourceByte] using ha
      have hvalue := Option.some.inj ha'
      exact hvalue.symm.trans (hi offset hoffset)
    | write other =>
      have hwrite : candidate.view.writeByte other (base.add offset) = some (Scalar.u32Byte value offset) := by
        simpa [hs,sourceByte] using ha
      have hid := hu offset hoffset other _ hwrite
      exact False.elim (hmissing ⟨offset,hoffset,by simpa only [hid] using hs⟩)
  exact hn (Scalar.u32_bytes_injective hv (by decide) hbytes)

theorem release_acquire_of_nonzero_u32 {candidate initial rf co read writer base value}
    (hm : MemoryConditions candidate initial rf co)
    (hr : candidate.view.eventAt read = some (.read base (Scalar.u32Bytes value)))
    (he : ∀ offset, offset < 4 → Eligible candidate rf read (base.add offset))
    (hi : Scalar.RepresentsU32 initial base 0) (hv : value < 2^32) (hn : value ≠ 0)
    (hu : ∀ offset, offset < 4 → ∀ other v, candidate.view.writeByte other (base.add offset) = some v → other = writer)
    (hrelease : (candidate.kindAt writer).map Kind.order = some .release)
    (hacquire : (candidate.kindAt read).map Kind.order = some .acquire)
    (hs : MorallyStrong candidate writer read) : ReleaseAcquireSync candidate rf writer read := by
  obtain ⟨offset,hoffset,hsource⟩ := nonzero_u32_read_observes_writer hm hr he hi hv hn hu
  have hread : candidate.view.readByte read (base.add offset) = some (Scalar.u32Byte value offset) := by
    simpa only [Ptx.Event.Candidate.readByte,hr,Option.bind_some,Ptx.Event.Kind.readByte]
      using Scalar.u32_payload_byte base value offset hoffset
  have hvalue := hm.agreement read (base.add offset) _ (he offset hoffset) hread
  have hwrite : candidate.view.writeByte writer (base.add offset) = some (Scalar.u32Byte value offset) := by
    simpa [hsource,sourceByte] using hvalue
  exact ⟨hrelease,hacquire,hs,.direct ⟨hs,base.add offset,Scalar.u32Byte value offset,hread,hsource,by rw [hwrite]; rfl⟩⟩

end
end Ptx.Ordered
