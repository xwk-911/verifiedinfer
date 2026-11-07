import Ptx.Kernels.AmpereTiledSharedWriters

/-! Actual in-range copy writes and packed shared reads exist at every byte of
their footprints. These facts assert neither memory agreement nor eligibility. -/
namespace Ptx.AmpereTiledAccesses
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledTrace Ptx.AmpereTiledEvents Ptx.AmpereTiledGraph
noncomputable section

theorem payload_exists (base : Location) (bytes : List Symbolic.Byte) {offset : Nat} (ho : offset < bytes.length) :
    ∃ value, Ptx.Event.payloadByte base bytes (base.add offset) = some value := by
  rw [Ptx.Event.payloadByte_offset]
  exact ⟨bytes[offset],List.getElem?_eq_getElem ho⟩

theorem read_byte_exists {cfg launch candidate} (h : SourceInfo cfg launch candidate) {id : ThreadId}
    (hv : id.Valid launch.geometry) {phase : Nat} (hp : phase < cfg.k/16) (reg : Fin 6) (offset : Fin 4) :
    ∃ value, candidate.readByte (.thread ⟨id,17*phase+7+reg.val⟩)
      ((AmpereTiledInventory.readBase (context launch id) reg).add offset.val) = some value := by
  have hs : 7+reg.val < 17 := by have hh := reg.isLt; omega
  obtain ⟨t,ht,hid,r,he⟩ := phase_view h hv hp hs
  subst id
  have hread : candidate.eventAt ⟨t.id,17*phase+7+reg.val⟩ = some (.ordinary (.read (AmpereTiledInventory.readBase (context launch t.id) reg)
      (AmpereTiledInventory.readPair r phase reg).encode)) := by
    simpa only [Nat.add_assoc] using he.trans (AmpereTiledInventory.phase_read _ _ _ _ phase reg)
  obtain ⟨value,hvalue⟩ := payload_exists (AmpereTiledInventory.readBase (context launch t.id) reg)
    (AmpereTiledInventory.readPair r phase reg).encode (offset := offset.val) (by simpa using offset.isLt)
  exact ⟨value,by simpa [Candidate.readByte,Candidate.memoryKind,hread,Ptx.Event.Kind.readByte] using hvalue⟩

theorem copy_write_byte_exists {cfg launch candidate} (h : SourceInfo cfg launch candidate) {id : ThreadId}
    (hv : id.Valid launch.geometry) {phase : Nat} (hp : phase < cfg.k/16) (part : Fin 3) (offset : Fin 8) :
    ∃ value, candidate.writeByte (.copyWrite ⟨id,3*phase+part.val⟩)
      ⟨.shared id.cta,AmpereTiledSharedWriters.copyBase id part+offset.val⟩ = some value := by
  obtain ⟨t,ht,hid,r,he⟩ := phase_view h hv hp (by have hh := part.isLt; omega : part.val < 17)
  subst id
  rw [AmpereTiledInventory.phase_issue] at he
  have hcopy := event_issue_has_copy h.formed he
  have hvalid : (context launch t.id).id.Valid (geometry cfg) := by simpa only [context,h.geometry] using hv
  have hdst := operation_destination (cfg := cfg) (context launch t.id) t.oracle r hvalid phase part
  change (operationAt cfg (context launch t.id) t.oracle r phase part).dst =
    ⟨.shared t.id.cta,AmpereTiledSharedWriters.copyBase t.id part⟩ at hdst
  obtain ⟨value,hvalue⟩ := payload_exists (operationAt cfg (context launch t.id) t.oracle r phase part).dst
    (operationAt cfg (context launch t.id) t.oracle r phase part).bytes (offset := offset.val)
    (by rw [operation_size _ _ _ _ phase hp part]; exact offset.isLt)
  rw [hdst] at hvalue
  exact ⟨value,by simpa [Candidate.writeByte,Candidate.memoryKind,hcopy,hdst,Ptx.Event.Kind.writeByte,Location.add] using hvalue⟩

end
end Ptx.AmpereTiledAccesses
