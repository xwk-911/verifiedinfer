import Ptx.Kernels.AmpereTiledRace
import Ptx.Event.Publication

/-! Visibility for every memory-admitted actual candidate. Eligibility is now
derived from the complete source graph, rather than supplied by the caller. -/
namespace Ptx.AmpereTiledMemory
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledGraph Ptx.AmpereTiledEvents
noncomputable section

theorem global_input_source {cfg launch candidate rf co read loc observed} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co) (hs : loc.space = .global)
    (hr : candidate.readByte read loc = some observed) : rf read loc = none := by
  cases he : rf read loc with
  | none => rfl
  | some writer =>
    have hw := MemoryGraph.write_read_value hm.agreement (AmpereTiledRace.eligible h rf read loc) hr he
    rw [graph_writeByte,AmpereTiledGlobalAccesses.global_read_unwritten h hs hr writer] at hw
    cases hw

theorem global_input_value {cfg launch candidate rf co read loc observed} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co) (hs : loc.space = .global)
    (hr : candidate.readByte read loc = some observed) : observed = launch.initial loc :=
  MemoryGraph.initial_read_value hm.agreement (AmpereTiledRace.eligible h rf read loc) hr (global_input_source h hm hs hr)

theorem current_copy_source {cfg launch candidate rf co} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co)
    {writer reader : ThreadId} (hw : writer.Valid launch.geometry) (hr : reader.Valid launch.geometry)
    (hcta : writer.cta = reader.cta) {phase : Nat} (hp : phase < cfg.k/16) (part : Fin 3) (reg : Fin 6)
    {loc written observed} (hs : loc.space = .shared reader.cta)
    (hcw : candidate.writeByte (.copyWrite ⟨writer,3*phase+part.val⟩) loc = some written)
    (hcr : candidate.readByte (.thread ⟨reader,17*phase+7+reg.val⟩) loc = some observed) :
    rf (.thread ⟨reader,17*phase+7+reg.val⟩) loc = some (.copyWrite ⟨writer,3*phase+part.val⟩) :=
  AmpereTiledPhaseVisibility.current_copy_source h hm hw hr hcta hp part reg hs (AmpereTiledRace.eligible h rf _ _) hcw hcr

theorem current_copy_value {cfg launch candidate rf co} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co)
    {writer reader : ThreadId} (hw : writer.Valid launch.geometry) (hr : reader.Valid launch.geometry)
    (hcta : writer.cta = reader.cta) {phase : Nat} (hp : phase < cfg.k/16) (part : Fin 3) (reg : Fin 6)
    {loc written observed} (hs : loc.space = .shared reader.cta)
    (hcw : candidate.writeByte (.copyWrite ⟨writer,3*phase+part.val⟩) loc = some written)
    (hcr : candidate.readByte (.thread ⟨reader,17*phase+7+reg.val⟩) loc = some observed) : observed = written :=
  AmpereTiledPhaseVisibility.current_copy_value h hm hw hr hcta hp part reg hs (AmpereTiledRace.eligible h rf _ _) hcw hcr

theorem copy_source_global {cfg launch candidate operation op} (h : SourceInfo cfg launch candidate)
    (hc : candidate.copyAt operation = some op) : op.src.space = .global := by
  obtain ⟨t,ht,r,phase,hphase,part,_,hop⟩ := copy_cases h hc
  have hv : (context launch t.id).id.Valid (geometry cfg) := by
    simpa only [h.geometry,context] using (h.formed.2.2.1 t ht).1
  rw [hop,operation_source h.layout (context launch t.id) t.oracle r hv h.active phase hphase part]

theorem copy_payload_initial {cfg launch candidate rf co operation op} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co) (hc : candidate.copyAt operation = some op)
    {offset : Nat} (ho : offset < op.bytes.length) :
    op.bytes[offset] = launch.initial (op.src.add offset) := by
  have hr : candidate.readByte (.copyRead operation) (op.src.add offset) = some op.bytes[offset] := by
    simp only [Candidate.readByte,Candidate.memoryKind,hc,Option.map_some,Option.bind_some,Ptx.Event.Kind.readByte,
      Ptx.Event.payloadByte_offset,List.getElem?_eq_getElem ho]
  exact global_input_value h hm (copy_source_global h hc) hr

/-- Copy writes carry exactly the bytes constrained at the separate read node.
The byte offset connects global input and shared destination; no copy value is
introduced as an external assumption. -/
theorem copy_written_value {cfg launch candidate rf co operation op loc written} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co) (hc : candidate.copyAt operation = some op)
    (hw : candidate.writeByte (.copyWrite operation) loc = some written) :
    ∃ offset, offset < op.bytes.length ∧ loc = op.dst.add offset ∧ written = launch.initial (op.src.add offset) := by
  have hp : Ptx.Event.payloadByte op.dst op.bytes loc = some written := by
    simpa [Candidate.writeByte,Candidate.memoryKind,hc,Ptx.Event.Kind.writeByte] using hw
  obtain ⟨offset,ho,rfl⟩ := Ptx.Event.payload_location hp
  have hv : op.bytes[offset] = written := by
    rw [Ptx.Event.payloadByte_offset,List.getElem?_eq_getElem ho] at hp
    exact Option.some.inj hp
  exact ⟨offset,ho,rfl,hv.symm.trans (copy_payload_initial h hm hc ho)⟩

theorem shared_input_value {cfg launch candidate rf co} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co)
    {writer reader : ThreadId} (hw : writer.Valid launch.geometry) (hr : reader.Valid launch.geometry)
    (hcta : writer.cta = reader.cta) {phase : Nat} (hp : phase < cfg.k/16) (part : Fin 3) (reg : Fin 6)
    {op loc written observed} (hs : loc.space = .shared reader.cta)
    (hc : candidate.copyAt ⟨writer,3*phase+part.val⟩ = some op)
    (hcw : candidate.writeByte (.copyWrite ⟨writer,3*phase+part.val⟩) loc = some written)
    (hcr : candidate.readByte (.thread ⟨reader,17*phase+7+reg.val⟩) loc = some observed) :
    ∃ offset, offset < op.bytes.length ∧ loc = op.dst.add offset ∧ observed = launch.initial (op.src.add offset) := by
  obtain ⟨offset,ho,hl,hvalue⟩ := copy_written_value h hm hc hcw
  exact ⟨offset,ho,hl,(current_copy_value h hm hw hr hcta hp part reg hs hcw hcr).trans hvalue⟩

end
end Ptx.AmpereTiledMemory
