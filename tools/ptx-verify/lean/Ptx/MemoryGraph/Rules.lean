import Ptx.MemoryGraph.Core

/-! Byte visibility rules for the graph-parametric generic memory model.
Eligibility is derived from races; it is never replaced by True for async reads.
-/
namespace Ptx.MemoryGraph
open Ptx.ISA
open Ptx.Event (ByteMap)
variable {Node ByteValue Source : Type} [Sources Node Source]

theorem initial_read_value {c : Graph Node ByteValue} {initial eligible read loc value} {rf : ReadsFrom Node Source}
    (ha : ValueAgreement c initial eligible rf) (he : eligible read loc)
    (hr : c.readByte read loc = some value) (hs : rf read loc = initialSource) : value = initial loc := by
  have h := ha read loc value he hr
  rw [hs,sourceByte_initial] at h
  exact (Option.some.inj h).symm
theorem write_read_value {c : Graph Node ByteValue} {initial eligible read loc value writer} {rf : ReadsFrom Node Source}
    (ha : ValueAgreement c initial eligible rf) (he : eligible read loc)
    (hr : c.readByte read loc = some value) (hs : rf read loc = writeSource writer) : c.writeByte writer loc = some value := by
  have h := ha read loc value he hr
  simpa only [hs,sourceByte_write] using h
theorem unwritten_read_initial {c : Graph Node ByteValue} {initial eligible read loc value} {rf : ReadsFrom Node Source}
    (ha : ValueAgreement c initial eligible rf) (he : eligible read loc) (hr : c.readByte read loc = some value)
    (hn : ∀ writer, c.writeByte writer loc = none) : value = initial loc := by
  rcases source_cases (rf read loc) with hs | ⟨writer,hs⟩
  · exact initial_read_value ha he hr hs
  · have hh := write_read_value ha he hr hs
    rw [hn writer] at hh
    cases hh

theorem causal_of_base {c : Graph Node ByteValue} {rf : ReadsFrom Node Source} {a b}
    (ho : c.Overlap a b) (hb : c.base a b) : Causality c rf a b := .inl ⟨ho,hb⟩
theorem stale_initial_forbidden {c : Graph Node ByteValue} {initial co writer read loc vw vr} {rf : ReadsFrom Node Source}
    (hc : MemoryConditions c initial rf co) (hm : ¬ MixedSizeRace c rf)
    (hw : c.writeByte writer loc = some vw) (hr : c.readByte read loc = some vr)
    (hb : Causality c rf writer read) : rf read loc ≠ initialSource := by
  intro hs
  exact (hc.causality hm).noStale writer read loc vw vr hw hr hb
    (hs ▸ (hc.coherence hm).initialization loc writer vw hw)
theorem unique_writer_visible {c : Graph Node ByteValue} {initial co writer read loc vw vr} {rf : ReadsFrom Node Source}
    (hc : MemoryConditions c initial rf co) (he : Eligible c rf read loc)
    (hw : c.writeByte writer loc = some vw) (hr : c.readByte read loc = some vr)
    (hb : Causality c rf writer read)
    (hu : ∀ other value, c.writeByte other loc = some value → other = writer) : vr = vw := by
  rcases source_cases (rf read loc) with hs | ⟨other,hs⟩
  · exact (stale_initial_forbidden hc he.1 hw hr hb hs).elim
  · have hv := write_read_value hc.agreement he hr hs
    have hi := hu other vr hv
    subst other
    exact Option.some.inj (hv.symm.trans hw)

/-- A reusable buffer may have many writers. The selected phase's write is
visible when every other write is earlier than it or later than this read.
These are order obligations against the actual graph, not an assumed read
value, chosen rf, or restriction on allowed memory witnesses. -/
theorem phase_writer_source {c : Graph Node ByteValue} {initial co writer read loc vw vr} {rf : ReadsFrom Node Source}
    (hc : MemoryConditions c initial rf co) (he : Eligible c rf read loc)
    (hw : c.writeByte writer loc = some vw) (hr : c.readByte read loc = some vr)
    (hb : Causality c rf writer read)
    (hphase : ∀ other value, c.writeByte other loc = some value →
      other = writer ∨ Causality c rf other writer ∨ Causality c rf read other) :
    rf read loc = writeSource writer := by
  rcases source_cases (rf read loc) with hs | ⟨other,hs⟩
  · exact (stale_initial_forbidden hc he.1 hw hr hb hs).elim
  · have hv := write_read_value hc.agreement he hr hs
    rcases hphase other vr hv with hid | hbefore | hafter
    · exact hid ▸ hs
    · have hco := (hc.coherence he.1).causality loc other writer vr vw hv hw hbefore
      exact ((hc.causality he.1).noStale writer read loc vw vr hw hr hb (hs ▸ hco)).elim
    · exact ((hc.causality he.1).noFuture read other loc vr vr hr hv hafter hs).elim

theorem phase_writer_visible {c : Graph Node ByteValue} {initial co writer read loc vw vr} {rf : ReadsFrom Node Source}
    (hc : MemoryConditions c initial rf co) (he : Eligible c rf read loc)
    (hw : c.writeByte writer loc = some vw) (hr : c.readByte read loc = some vr)
    (hb : Causality c rf writer read)
    (hphase : ∀ other value, c.writeByte other loc = some value →
      other = writer ∨ Causality c rf other writer ∨ Causality c rf read other) : vr = vw := by
  have hs := phase_writer_source hc he hw hr hb hphase
  have hv := write_read_value hc.agreement he hr hs
  exact Option.some.inj (hv.symm.trans hw)

theorem race_free_eligible {c : Graph Node ByteValue} {rf : ReadsFrom Node Source}
    (hn : ∀ a b, ¬ DataRace c rf a b) (read loc) : Eligible c rf read loc := by
  constructor
  · rintro ⟨a,b,hr,_⟩
    exact hn a b hr
  · rintro (⟨_,_,hr⟩ | ⟨a,b,_,_,hr⟩)
    · exact hn _ _ hr
    · exact hn a b hr

theorem data_race_symm {c : Graph Node ByteValue} {rf : ReadsFrom Node Source} {a b}
    (hr : DataRace c rf a b) : DataRace c rf b a := by
  refine ⟨?_,hr.conflict.symm,hr.notBackward,hr.notForward,?_⟩
  · rcases hr.overlap with ⟨loc,ha,hb⟩
    exact ⟨loc,hb,ha⟩
  · rintro ⟨he | ⟨sb,sa,hb,ha,hsb,hsa⟩,footprint,hbf,haf⟩
    · exact hr.notStrong ⟨.inl he.symm,footprint,haf,hbf⟩
    · exact hr.notStrong ⟨.inr ⟨sa,sb,ha,hb,hsa,hsb⟩,footprint,haf,hbf⟩

theorem ordered_conflicts_no_races {c : Graph Node ByteValue} {rf : ReadsFrom Node Source}
    (horder : ∀ a b, c.Overlap a b → (c.Writes a ∨ c.Writes b) →
      MorallyStrong c a b ∨ Causality c rf a b ∨ Causality c rf b a) (a b) : ¬ DataRace c rf a b := by
  intro hr
  rcases horder a b hr.overlap hr.conflict with hs | hf | hb
  · exact hr.notStrong hs
  · exact hr.notForward hf
  · exact hr.notBackward hb

end Ptx.MemoryGraph
