import Ptx.Kernels.AmpereTiledSharedWriters

/-! Instantiate the generic repeated-write rule on actual tiled PTX candidates.
Every competing shared writer is current, earlier, or later than the read.
Eligibility remains explicit until the full race-freedom proof is discharged. -/
namespace Ptx.AmpereTiledPhaseVisibility
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledTrace Ptx.AmpereTiledGraph
open Ptx.AmpereTiledPhaseOrder Ptx.AmpereTiledSharedWriters
noncomputable section

theorem writer_classification {cfg launch candidate} {rf : Ampere.ReadsFrom} (h : SourceInfo cfg launch candidate)
    {writer reader : ThreadId} (hw : writer.Valid launch.geometry) (hr : reader.Valid launch.geometry)
    (hcta : writer.cta = reader.cta) {phase : Nat} (hp : phase < cfg.k/16) (part : Fin 3) (reg : Fin 6)
    {loc written observed} (hs : loc.space = .shared reader.cta)
    (hcw : candidate.writeByte (.copyWrite ⟨writer,3*phase+part.val⟩) loc = some written)
    (hcr : candidate.readByte (.thread ⟨reader,17*phase+7+reg.val⟩) loc = some observed)
    (other : Node) (value : Symbolic.Byte) (ho : candidate.writeByte other loc = some value) :
    other = .copyWrite ⟨writer,3*phase+part.val⟩ ∨
      MemoryGraph.Causality candidate.memoryGraph rf other (.copyWrite ⟨writer,3*phase+part.val⟩) ∨
      MemoryGraph.Causality candidate.memoryGraph rf (.thread ⟨reader,17*phase+7+reg.val⟩) other := by
  obtain ⟨t,ht,r,otherPhase,hotherPhase,otherPart,hn,hspace,_,_⟩ := shared_write_info h hs ho
  have hv : t.id.Valid launch.geometry := (h.formed.2.2.1 t ht).1
  have howner : t.id.cta = reader.cta := AddressSpace.shared.inj (hspace.symm.trans hs)
  subst other
  rcases Nat.lt_trichotomy otherPhase phase with hbefore | heq | hafter
  · refine .inr (.inl (MemoryGraph.causal_of_base ?_ ?_))
    · exact ⟨loc,.inr (by simp [ho]),.inr (by simp [hcw])⟩
    · exact copy_before_later_copy h hv hw (howner.trans hcta.symm) hbefore hp otherPart part
  · subst otherPhase
    exact .inl (phase_unique h hs ho hcw rfl rfl)
  · refine .inr (.inr (MemoryGraph.causal_of_base ?_ ?_))
    · exact ⟨loc,.inl (by simp [hcr]),.inr (by simp [ho])⟩
    · exact read_before_later_copy h hr hv howner.symm hafter hotherPhase reg otherPart

theorem current_copy_source {cfg launch candidate rf co} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co)
    {writer reader : ThreadId} (hw : writer.Valid launch.geometry) (hr : reader.Valid launch.geometry)
    (hcta : writer.cta = reader.cta) {phase : Nat} (hp : phase < cfg.k/16) (part : Fin 3) (reg : Fin 6)
    {loc written observed} (hs : loc.space = .shared reader.cta)
    (he : MemoryGraph.Eligible candidate.memoryGraph rf (.thread ⟨reader,17*phase+7+reg.val⟩) loc)
    (hcw : candidate.writeByte (.copyWrite ⟨writer,3*phase+part.val⟩) loc = some written)
    (hcr : candidate.readByte (.thread ⟨reader,17*phase+7+reg.val⟩) loc = some observed) :
    rf (.thread ⟨reader,17*phase+7+reg.val⟩) loc = some (.copyWrite ⟨writer,3*phase+part.val⟩) := by
  refine MemoryGraph.phase_writer_source (c := candidate.memoryGraph) hm he hcw hcr ?_ ?_
  · refine MemoryGraph.causal_of_base ?_ (copy_before_read h hw hr hcta hp part reg)
    exact ⟨loc,.inr (by simp [hcw]),.inl (by simp [hcr])⟩
  · exact writer_classification h hw hr hcta hp part reg hs hcw hcr

theorem current_copy_value {cfg launch candidate rf co} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co)
    {writer reader : ThreadId} (hw : writer.Valid launch.geometry) (hr : reader.Valid launch.geometry)
    (hcta : writer.cta = reader.cta) {phase : Nat} (hp : phase < cfg.k/16) (part : Fin 3) (reg : Fin 6)
    {loc written observed} (hs : loc.space = .shared reader.cta)
    (he : MemoryGraph.Eligible candidate.memoryGraph rf (.thread ⟨reader,17*phase+7+reg.val⟩) loc)
    (hcw : candidate.writeByte (.copyWrite ⟨writer,3*phase+part.val⟩) loc = some written)
    (hcr : candidate.readByte (.thread ⟨reader,17*phase+7+reg.val⟩) loc = some observed) : observed = written := by
  have hsource := current_copy_source h hm hw hr hcta hp part reg hs he hcw hcr
  have hv := MemoryGraph.write_read_value hm.agreement he hcr hsource
  exact Option.some.inj (hv.symm.trans hcw)

end
end Ptx.AmpereTiledPhaseVisibility
